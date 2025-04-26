import os
import re
import sys
from collections import defaultdict
from typing import List, Tuple, Optional


# Regular expression: Match variable names, including '|', '\|', and common name
variable_name = r'(\|[^|]*?(?:\\\|[^|]*?)*\||[^\s()]+)'
variable_pattern = re.compile(r'(\|[^|]*?(?:\\\|[^|]*?)*\||[^\s()]+)')
# Regular expression: Match variable names in declare-fun statement
declare_pattern = re.compile(rf'\(declare-fun\s+{variable_name}\s*\(')
# Regular expression: Match variable names in assert statement
# (assert var_name) or (assert (not var_name))
assert_pattern = re.compile(rf'^\(assert\s+\(?\s*(not\s+)?(?P<var>{variable_name})')


# Non SMT variable name
non_variables = ['true', 'false', '()', 'not', 'and', 'or', '=>', 
                '=', '<', '<=', '>', '>=', 'bvule', 'ite', 'let']

# Symbolic Route and Symbolic Packet target string
symbolic_variables = ['_metric', '_localPref', '_adminDist', '_med', '_bgpInternal', 
                      '_igpMetric', '_ospfType', '_ospfArea', '_routerID', 
                      '_prefixLength', '_permitted', '_community_', 'clientId', 
                      'dst-ip', 'src-ip', 'dst-port', 'src-port', 'icmp-code', 
                      'icmp-type', 'tcp-ack', 'tcp-cwr', 'tcp-ece', 'tcp-fin', 'tcp-psh',
                      'tcp-rst', 'tcp-syn', 'tcp-urg', 'ip-protocol']


def is_variable(expr: str) -> bool:
    expr = expr.strip()

    # Disqualify empty or obvious operators/literals
    if expr in non_variables:
        return False
    if expr.startswith('#') or expr.startswith('(') or expr.startswith('"'):
        return False
    if re.match(r'^\d+(\.\d+)?$', expr):  # purely numeric
        return False
    if expr[0].isdigit():
        return False
    if expr.endswith(')') and not expr.startswith('|'):
        return False

    return True

def parse_equal_expr(expr: str):
    expr = expr.strip()
    if not expr.startswith('(='):
        return None, None

    tokens = []
    current = ''
    depth = 0
    i = 2  # skip "(="
    while i < len(expr):
        ch = expr[i]
        if ch == '(':
            depth += 1
            current += ch
        elif ch == ')':
            depth -= 1
            current += ch
        elif ch.isspace() and depth == 0:
            if current.strip():
                tokens.append(current.strip())
                current = ''
        else:
            current += ch
        i += 1

    if current.strip():
        tokens.append(current.strip())

    if len(tokens) != 2:
        return None, None

    return tokens[0], tokens[1]

def split_and_expr(and_expr: str) -> list[str]:
    """Split (and expr1 expr2 ...) into individual exprs."""
    and_expr = and_expr.strip()
    if and_expr.startswith('(and'):
        and_expr = and_expr[len('(and'):].strip()

    and_exprs = []
    depth = 0
    current = []

    for ch in and_expr:
        if ch == '(':
            depth += 1
            current.append(ch)
        elif ch == ')':
            current.append(ch)
            depth -= 1
        elif ch == ' ' and depth == 0:
            if current:
                and_exprs.append(''.join(current).strip())
                current = []
        else:
            current.append(ch)

    if current:
        and_exprs.append(''.join(current).strip())

    return and_exprs

def extract_assert_expressions(smt2_lines: list[str]) -> list[str]:
    """Extract assert expression from the smt encoding lines"""
    assert_exprs = []
    current_expr = ''
    depth = 0
    in_assert = False

    for line in smt2_lines:
        line = line.strip()
        if not line or line.startswith(';'):
            continue

        if '(assert' in line:
            in_assert = True

        if in_assert:
            current_expr += ' ' + line
            depth += line.count('(') - line.count(')')
            if depth == 0:
                if current_expr.strip().startswith('(assert'):
                    assert_exprs.append(current_expr.strip())
                current_expr = ''
                in_assert = False

    return assert_exprs

def extract_declare_fun_expressions(smt2_lines: list[str]) -> list[str]:
    """Extract declare-fun expression from the smt encoding lines"""
    declare_exprs = []
    current_expr = ''
    depth = 0
    in_declare = False

    for line in smt2_lines:
        line = line.strip()
        if not line or line.startswith(';'):
            continue

        if '(declare-fun' in line:
            in_declare = True

        if in_declare:
            current_expr += ' ' + line
            depth += line.count('(') - line.count(')')
            if depth == 0:
                if current_expr.strip().startswith('(declare-fun'):
                    declare_exprs.append(current_expr.strip())
                current_expr = ''
                in_declare = False

    return declare_exprs

def extract_let_parts(line: str) -> Tuple[Optional[str], Optional[str]]:
    """Extract the bindings and body of a `let` expression"""
    if not line.startswith("(assert (let"):
        return None, None

    i = line.find("(let")
    stack = []
    start = i
    i += 4  # skip "(let"

    # Skip whitespace
    while i < len(line) and line[i] in " \n\t":
        i += 1

    # Expecting bindings block to start with '('
    if line[i] != '(':
        return None, None

    # Parse the bindings block
    bindings_start = i
    stack.append('(')
    i += 1
    while i < len(line) and stack:
        if line[i] == '(':
            stack.append('(')
        elif line[i] == ')':
            stack.pop()
        i += 1
    bindings_block = line[bindings_start:i].strip()

    # Skip whitespace
    while i < len(line) and line[i] in " \n\t":
        i += 1

    # Parse the body
    body_start = i
    stack = ['(']
    i += 1
    while i < len(line) and stack:
        if line[i] == '(':
            stack.append('(')
        elif line[i] == ')':
            stack.pop()
        i += 1
    body = line[body_start:i].strip()

    return bindings_block, body

def extract_bindings(bindings_block: str) -> List[Tuple[str, str]]:
    """Extract variables and their corresponding expressions from the `let` bindings block"""
    bindings = []
    i = 0
    n = len(bindings_block)
    
    while i < n:
        # Skip any whitespace
        while i < n and bindings_block[i].isspace():
            i += 1
        
        # Start of a binding tuple (var expr)
        if i < n and bindings_block[i] == '(':
            i += 1  # Skip the opening '('
            
            # Extract variable name (ignoring the leading '(' and any trailing spaces)
            start = i
            while i < n and not bindings_block[i].isspace() and bindings_block[i] != ')':
                i += 1
            var = bindings_block[start:i]

            # Strip the leading '(' if it exists in the variable name
            if var.startswith('('):
                var = var[1:]

            # Skip whitespace between var and expr
            while i < n and bindings_block[i].isspace():
                i += 1
            
            # Extract expression, handling nested parentheses
            if i < n and bindings_block[i] == '(':
                count = 1
                expr_start = i
                i += 1
                while i < n and count > 0:
                    if bindings_block[i] == '(':
                        count += 1
                    elif bindings_block[i] == ')':
                        count -= 1
                    i += 1
                expr = bindings_block[expr_start:i]
            else:
                # For non-parenthesized expressions (e.g., constants or symbols)
                expr_start = i
                while i < n and bindings_block[i] != ')':
                    i += 1
                expr = bindings_block[expr_start:i]
            
            # Strip extra whitespace around expressions
            bindings.append((var.strip(), expr.strip()))
        
        # Move to the next potential binding
        while i < n and bindings_block[i] != '(':
            i += 1
    
    return bindings

def replace_vars(body: str, bindings: List[Tuple[str, str]]) -> str:
    """Replace variables in the body of a `let` expression with their corresponding expressions"""
    for var, expr in reversed(bindings):
        # Wrap the expression in parentheses if it's not already wrapped
        expr_wrapped = f"({expr})" if not expr.startswith("(") else expr
        # Ensure that the variable is properly matched, even when it contains special characters
        # Using a more robust regex pattern to match standalone variable names
        pattern = rf"(?<![\w!]){re.escape(var)}(?![\w\d!])"
        # Use re.sub to replace the variable in the body with its expression
        body = re.sub(pattern, expr_wrapped, body)
    return body

def expand_one_let(line: str) -> str:
    """Expand the outermost `let` sub-expression in a line"""
    bindings_block, body = extract_let_parts(line)
    if bindings_block is None or body is None:
        return line
    bindings = extract_bindings(bindings_block)

    # Replace the variables in the body with their expressions
    body = replace_vars(body, bindings)

    return f"(assert {body})"

def expand_let_expressions(smt_lines: List[str]) -> List[str]:
    """Expand the outermost `let` expressions in each line"""
    expanded_lines = []
    for line in smt_lines:
        while "(let" in line:
            line = expand_one_let(line)  # Only expand the outermost `let`
        expanded_lines.append(line)
    return expanded_lines

def extract_variables_from_asserts(assert_exprs: list[str]) -> dict[str, list[str]]:
    """Extract variable names and relevant expressions in equal expression lines from SMT encoding"""
    filtered_vars = defaultdict(list)  # key: var, value: list of expr

    for expr in assert_exprs:
        expr = expr.strip()

        # Handle (assert (= left_expr right_expr))
        if expr.startswith('(assert (='):
            # Remove the outer part: (assert ...)
            inner_expr = expr[len('(assert'):-len(')')].strip()
            left_expr, right_expr = parse_equal_expr(inner_expr)
            if left_expr is None or right_expr is None:
                continue
            for side_expr in (left_expr, right_expr):
                side_expr = side_expr.rstrip(')')  # Remove extra right parenthesis
                if is_variable(side_expr):
                    filtered_vars[side_expr].append(expr)
            continue

        # Handle (assert (and sub-expr1 sub-expr2 ...))
        # and all sub-exprssions are mkEq expression
        if expr.startswith('(assert (and'):
            # Remove the outer part: (assert ...)
            inner_expr = expr[len('(assert'):-len(')')].strip()
            sub_exprs = split_and_expr(inner_expr)
        
            all_eq = True
            eq_exprs = []
            for sub in sub_exprs:
                sub = sub.strip()
                if sub.startswith('(='):
                    eq_exprs.append(sub)
                else:
                    all_eq = False
                    break
        
            if not all_eq:
                continue
        
            for eq_expr in eq_exprs:
                fake_assert = f'(assert {eq_expr})'
                sub_vars = extract_variables_from_asserts([fake_assert])
                for var, _ in sub_vars.items():
                    filtered_vars[var].append(expr)
            continue

        """
        # Handle (assert (= (or |VAR| |VAR| ...) |VALUE|))
        if expr.startswith('(assert (=' ):
            inner = expr[len('(assert (='):].strip()
            if inner.endswith('))'):
                inner = inner[:-2].strip()  # Remove the two last ')'

                if inner.startswith('(or '):
                    # Fix the approach to handle parentheses correctly in variable names
                    or_start = inner.find('(or ') + len('(or ')  # Start right after '(or '
                    or_end = inner.find(')', or_start)  # Find the closing parenthesis of the OR

                    # Extract the OR part (all the expressions between (or ...))
                    or_expr = inner[or_start:or_end].strip()

                    # Extract the right part (after the closing parenthesis of the OR)
                    right_expr = inner[or_end + 1:].strip()

                    # Use regular expression to extract variables from the or_expr
                    var_pattern = r'\|[^\|]*\|'  # Matches |VAR| format, allowing any characters inside | |
                    vars_in_or = re.findall(var_pattern, or_expr)

                    if vars_in_or:
                        # print(expr)
                        # print('OR vars:', vars_in_or)
                        for var in vars_in_or:
                            filtered_vars[var].append(expr)
                        continue  # Continue processing with the next expr if an OR is found
        """

        # Handle (assert (bvule expr number))
        """
        if expr.startswith('(assert (bvule'):
            # Remove the outer part: (assert (bvule ...))
            inner_expr = expr[len('(assert (bvule'):-len('))')].strip()
            match_variables = variable_pattern.findall(inner_expr)
            for var in match_variables:
                if is_variable(var):
                    filtered_vars[var].append(expr)
            continue
        """

        # Handle (assert (>= variable number)) or (assert (<= ...))
        """
        if expr.startswith('(assert (>=') or expr.startswith('(assert (<='):
            # Remove the outer part: (assert (>= ...))
            inner_expr = expr[len('(assert (>='):-len(')')].strip()
            match_variables = variable_pattern.findall(inner_expr)
            for var in match_variables:
                if is_variable(var):
                    filtered_vars[var].append(expr)
            continue
        """

        # Handle (assert (not (<= variable number))) or (assert (not (>= ...)))
        """
        if expr.startswith('(assert (not (<=') or expr.startswith('(assert (not (>='):
            # Remove the outer part: (assert (not (<= ...)))
            inner_expr = expr[len('(assert (not (<='):-len(')))')].strip()
            match_variables = variable_pattern.findall(inner_expr)
            for var in match_variables:
                if is_variable(var):
                    filtered_vars[var].append(expr)
            continue
        """

        # Handle (assert variable) and (assert (not variable))
        match = assert_pattern.match(expr)
        if match:
            var = match.group('var')
            if is_variable(var):
                filtered_vars[var].append(expr)

    return filtered_vars

def extract_variables_from_declares(declare_exprs: list[str]) -> list[str]:
    """Extract variable names in declare-fun expression lines from SMT encoding"""
    all_variables = []
    for expr in declare_exprs:
        match_variable = declare_pattern.findall(expr)
        all_variables.extend(match_variable)
    return all_variables

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: python filtered_equals_variable.py /your/path/to/work_directory")
        exit(1)

    path = sys.argv[1]

    smt_encoding_file = os.path.join(path, 'smt_encoding.smt2')
    filtered_variable_file = os.path.join(path, 'filtered_equals_variable.txt')
    other_variable_file = os.path.join(path, 'non_filtered_variable.txt')

    if not os.path.exists(smt_encoding_file):
        print(f"❌ Error: File not found: {smt_encoding_file}")
        exit(1)

    with open(smt_encoding_file, 'r', encoding='utf-8') as f:
        smt2_encoding = f.read()
        smt2_lines = smt2_encoding.splitlines()

    assert_exprs = extract_assert_expressions(smt2_lines)
    declare_exprs = extract_declare_fun_expressions(smt2_lines)

    # Expand let sub-expressions for all assert expressions
    assert_exprs = expand_let_expressions(assert_exprs)

    filtered_vars = extract_variables_from_asserts(assert_exprs)
    all_vars = extract_variables_from_declares(declare_exprs)

    other_symbolic_vars = []
    other_non_symbolic_vars = []
    for var in all_vars:
        if var in filtered_vars.keys():
            continue
        is_symbolic_variable = False
        for sym_str in symbolic_variables:
            if sym_str in var:
                is_symbolic_variable = True
                break
        if is_symbolic_variable:
            other_symbolic_vars.append(var + '\n')
        else:
            other_non_symbolic_vars.append(var + '\n')

    with open(filtered_variable_file, 'w', encoding='utf-8') as f:
        for var, exprs in filtered_vars.items():
            f.write(var + ':' + '\n')
            for expr in exprs:
                f.write(expr + '\n')
        """
        for var, _ in filtered_vars.items():
            f.write(var + '\n')
        """

    with open(other_variable_file, 'w', encoding='utf-8') as f:
        for var in other_non_symbolic_vars:
            f.write(var)
        f.write('\n')
        for var in other_symbolic_vars:
            f.write(var)

    print(f"📝 Total lines in smt encoding file: {len(smt2_lines)}")
    print(f"📝 Total declare-fun expressions lines in smt encoding file: {len(declare_exprs)}")
    print(f"📝 Total assert expressions lines in smt encoding file: {len(assert_exprs)}")
    print()
    print(f"🔍 Found variables: {len(all_vars)}")
    print(f"✅ Filtered variables count: {len(filtered_vars)}")
    print(f"❌ Other variables count (non-symbolic): {len(other_non_symbolic_vars)}")
    print(f"❌ Other variables count (symbolic): {len(other_symbolic_vars)}")
    print()
    print(f"📁 Wrote filtered variables to: {filtered_variable_file}")
    print(f"📁 Wrote other variables to: {other_variable_file}")
