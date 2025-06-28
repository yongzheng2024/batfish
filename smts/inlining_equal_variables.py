import os
import re
import sys
from collections import OrderedDict
from typing import List, Tuple, Optional

##########################################################################################
### global variables
##########################################################################################

definitions = OrderedDict()
simple_definitions = {}
composed_definitions = {}

target_variables = set()
cached_equal_variables = {}


##########################################################################################
### SMT2 variable regex and constant regex
### SMT2 assert experssions
##########################################################################################

# smt2 variable regex (supports quoted identifiers (|...|) and normal indentifiers)
var_regex =   r'(\|[^|]*?(?:\\\|[^|]*?)*\||[^\s()]+)'
var_pattern = re.compile(var_regex)
# smt2 constant regex (supports hex #xabc12345, or decimal 123)
# const_regex = r'(?:#[xX][0-9a-fA-F]+|\d+)'
const_regex = r'(#[xX][0-9a-fA-F]+|\d+)'
const_pattern = re.compile(const_regex)

# (assert (= V c)) and (assert (= c V))
pattern_eqvc = re.compile(rf'^\(assert\s+\(=\s+{var_regex}\s+{const_regex}\)\)$')
pattern_eqcv = re.compile(rf'^\(assert\s+\(=\s+{const_regex}\s+{var_regex}\)\)$')
# (assert (= V1 V2))
pattern_eqvv = re.compile(rf'^\(assert\s+\(=\s+{var_regex}\s+{var_regex}\)\)$')
# (assert (= V e)) and (assert (= e V))
pattern_eqve = re.compile(rf'^\(assert\s+\(=\s+{var_regex}\s+\((.+)\)\)\)$')
pattern_eqev = re.compile(rf'^\(assert\s+\(=\s+\((.+)\)\s+{var_regex}\)\)$')
# (assert (not V)) and (assert V)
pattern_not  = re.compile(rf'^\(assert\s+\(not\s+{var_regex}\)\)$')
pattern_true = re.compile(rf'^\(assert\s+{var_regex}\)$')
# (assert (and (= V1 e1) (= V2 e2) ...))
pattern_ands = re.compile(rf'^\(assert\s+\(and\s+(.*)\)\)$')


##########################################################################################
### print error information (you can use exit command to exit program when error happen)
##########################################################################################

def error_multi_exprs(var, exprs):
    print(f"ERROR: the variable ({var}) have multiple ({len(exprs)}) expressions, ")
    print("and now we can't handle these expressions:")
    for e in exprs:
        print(e)

def error_invalid_expr(expr):
    print(f"ERROR: the invalid expression:")
    print(expr)

def error_equal_variables_miss(expr):
    print(f"ERROR: the two equal variables both have not corresponding experssion:")
    print(expr)

def error_equal_variables_diff(expr):
    print(f"ERROR: the two equal variables have different corresponding experssion:")
    print(expr)

def is_simple_definition(def_expr):
    return (
        def_expr in {'true', 'false'} or
        re.fullmatch(r'#[xX][0-9a-fA-F]+', def_expr) or  # SMT hex constant
        re.fullmatch(r'\d+', def_expr)                   # decimal constant
    )

def is_composed_definition(def_expr):
    return None

##########################################################################################
### parse variable definitions (involving intermediate and configuration variable)
##########################################################################################

def parse_variable_definitions(variable_definitions_path):
    cached_definitions = set()
    lines = []

    def extract_assert_eqvc(expr):
        # Matches: (assert (= V c)) 
        # where V is a variable and c is a constant
        if (m := pattern_eqvc.match(expr)):
            return m.groups()
        return None

    def extract_assert_eqvv(expr):
        # Matches: (assert (= V1 V2)), (assert (= V2 V1))
        # where V1 and V2 are both variables
        if (m := pattern_eqvv.match(expr)):
            return m.groups()
        return None

    def extract_assert_eqve(expr):
        # Matches: (assert (= V e)), (assert (= e V))
        # where V is a variable and e is a complex expression
        if (m := pattern_eqve.match(expr)):
            return m.groups()
        if (m := pattern_eqev.match(expr)):
            return m.groups()
        return None

    def extract_assert_not(expr):
        # Matches: (assert (not V)) where V is a variable
        if (m := pattern_not.match(expr)):
            return m.group(1)
        return None

    def extract_assert_true(expr):
        # Matches: (assert V) where V is a variable
        if (m := pattern_true.match(expr)):
            return m.group(1)
        return None

    def extract_assert_ands(expr):
        # Matches: (assert (and ...))
        if (m := pattern_ands.match(expr)): 
            inner = m.group(1)
            return re.findall(r'\(=\s+(.+?)\s+(.+?)\)', inner)
        return []

    def handle_multi_exprs(var, exprs):
        """
        Process multiple expressions to extract equality or assertion relationships.
        Handles:
          - (assert (= X Y)) (assert (not X))  →  X = false, Y = false
          - (assert (not X)) (assert X)        →  X = true,  Y = true
        Applies the result to the global `definitions` map.
        """
        if len(exprs) != 2:
            print("ERROR: extract_and_eq expects exactly 2 expressions.")
            exit(1)
    
        lhs_var = rhs_var = None
    
        # Try to match equality pattern
        # Check match equality pattern, if not, print error information
        if (eqvv := next((pattern_eqvv.match(expr.strip())  \
                for expr in exprs if pattern_eqvv.match(expr.strip())), None)):
            lhs_var, rhs_var = eqvv.groups()
            lhs_var = lhs_var.strip()
            rhs_var = rhs_var.strip()
        else:
            error_multi_exprs(var, exprs)
            return 
    
        # Try to match assertion pattern (assert (not VAR)) or (assert VAR)
        match_flag = False
        for expr in exprs:
            expr = expr.strip() 
            if (m := pattern_not.match(expr)):
                var = m.group(1).strip()
                definitions[var] = "false"
                match_flag = True 
            elif (m := pattern_true.match(expr)):
                var = m.group(1).strip()
                definitions[var] = "true"
                match_flag = True
        # Check match assertion pattern, if not, print error information
        if not match_flag:
            error_multi_exprs(var, exprs)
            return

        # Finally add the equality if not overwritten
        if rhs_var not in definitions:
            definitions[rhs_var] = definitions[lhs_var]
        if lhs_var not in definitions:
            definitions[lhs_var] = definitions[rhs_var]

    with open(variable_definitions_path, 'r') as f:
        lines = [line.strip() for line in f if line.strip()]

    i = 0
    while i < len(lines):
        line = lines[i]
        # print(line)

        # If the line is not a variable, print error information and exit
        if not line.endswith(':'):
            error_invalid_expr(line)
            i += 1
            continue

        # Match var ending with colon (includes escaped characters safely)
        current_var = line.rstrip(':')
        i += 1
        if i >= len(lines):
            break

        # Extract the corresponding definition expressions of the variables
        current_defs = set()
        while i < len(lines) and not lines[i].strip().endswith(':'):
            current_defs.add(lines[i])
            i += 1

        # Warning: a variable has multiple corresponding definition expressions
        if len(current_defs) == 2:
            handle_multi_exprs(current_var, list(current_defs))
            continue
        elif len(current_defs) > 2:
            # TODO: implement more handle methods for multiple expressions
            # print error information (and exit)
            error_multi_exprs(current_var, current_defs)
            exit(1)

        # Normal: a variable has only one corresponding definition expression
        def_line = list(current_defs)[0]

        # Scenario 0
        if (eqvc := extract_assert_eqvc(def_line)):
            left, right = eqvc
            if left == current_var:
                definitions[current_var] = right
                continue

        # Scenario 1
        if (eqvv := extract_assert_eqvv(def_line)):
            cached_definitions.add(def_line)

        # Scenario 2
        if (eqve := extract_assert_eqve(def_line)):
            left, right = eqve
            if left == current_var:
                definitions[current_var] = right
                continue
            elif right == current_var:
                definitions[current_var] = left
                continue
            else:
                error_invalid_expr(def_line)
                exit(1)

        # Scenario 3
        if (not_var := extract_assert_not(def_line)):
            if (not_var != current_var):
                error_invalid_expr(def_line)
                exit(1)
            definitions[current_var] = "false"
            continue

        # Scenario 4
        if (true_var := extract_assert_true(def_line)):
            if (true_var != current_var):
                error_invalid_expr(def_line)
                exit(1)
            definitions[current_var] = "true"
            continue

        # Scenario 5, TODO
        for left, right in extract_assert_ands(def_line):
            if left == current_var:
                definitions[current_var] = right
                break
            elif right == current_var:
                definitions[current_var] = left
                break

    # Scenario 1
    for def_line in list(cached_definitions):
        if (eqvv := extract_assert_eqvv(def_line)):
            lhs_var, rhs_var = eqvv
            if lhs_var not in definitions and rhs_var not in definitions:
                error_equal_variables_miss(def_line)
                continue
            elif lhs_var in definitions and rhs_var not in definitions:
                definitions[rhs_var] = definitions[lhs_var]
                continue
            elif lhs_var not in definitions and rhs_var in definitions:
                definitions[lhs_var] = definitions[rhs_var]
                continue
            # lhs_var in definitions and rhs_var in definitions
            elif definitions[lhs_var] != definitions[rhs_var]:
                # TODO: Cache equal variables for other handle late.
                cached_equal_variables[lhs_var] = rhs_var
                cached_equal_variables[rhs_var] = lhs_var
                # print error information (and exit)
                error_equal_variables_diff(def_line)
                print(f"{lhs_var}: {definitions[lhs_var]}")
                print(f"{rhs_var}: {definitions[rhs_var]}")
                exit(1)

    return definitions


def extract_symbolic_variables(def_expr: str) -> set[str]:
    vals = var_pattern.findall(def_expr)

    sym_vars = set()
    for val in vals:
        if val in {'not', '<', '<=', '>', '>=', '=', 'and', 'or'}:
            continue
        if val in {'true', 'false'}:
            continue
        if re.fullmatch(r'\d+', val):                # decimal constant
            continue
        if re.fullmatch(r'#[xX][0-9a-fA-F]+', val):  # hex constant
            continue
        sym_vars.add(val)

    return sym_vars 


def replace_simple_definitions(def_expr: str, dep_vars: set[str]) -> str:
    for dep_var in dep_vars:
        escaped_var = re.escape(dep_var)
        def_expr = re.sub(escaped_var, definitions[dep_var], def_expr)
    return def_expr


def simplify_variable_definitions():
    to_remove = []
    for var, def_expr in definitions.items():
        if is_simple_definition(def_expr):
            continue
        composed_definitions[var] = f"({def_expr})"
        to_remove.append(var)

    for var in to_remove:
        del definitions[var]

    # FIXME: Improve simplifing variable definitions via topo-sort.
    #        * construct topo graph                       - O(cN) / O(n + e)
    #        * select the non-dependent node, iteratively - O(cN) / O(n + e)
    #                     ^------------
    #                     depend on external node or null node only

    changed_flag = True
    while changed_flag:
        changed_flag = False
        to_remove = []

        for var, def_expr in composed_definitions.items():
            deps = extract_symbolic_variables(def_expr)
            known_deps = [d for d in deps if d in definitions.keys()]
            unknown_deps = [d for d in deps if d not in definitions.keys()]

            if known_deps:
                composed_definitions[var] =  \
                    replace_simple_definitions(def_expr, known_deps)

            if unknown_deps:
                continue

            definitions[var] = replace_simple_definitions(def_expr, deps)
            to_remove.append(var)
            changed = True

        for var in to_remove:
            del composed_definitions[var]

    changed_flag = True
    while changed_flag:
        changed_flag = False
        to_remove = []

        for var, def_expr in composed_definitions.items():
            deps = extract_symbolic_variables(def_expr)
            error_deps = [d for d in deps if d in composed_definitions.keys()]

            if error_deps:
                continue

            definitions[var] = composed_definitions[var]
            to_remove.append(var)
            changed_flag = True

        for var in to_remove:
            del composed_definitions[var] 

    # if not composed_definitions:
    #     print("OK")
    # else:
    #     print(f"NO, {len(composed_definitions)}")


##########################################################################################
### load target variables (and delete these definitions)
##########################################################################################

def load_target_variables(target_variables_path):
    # Read all target variables
    with open(target_variables_path, 'r') as f:
        target_variables = set(line.strip() for line in f if line.strip())
    # Delete these target variables' definition
    for target_var in target_variables:
        if target_var in definitions.keys():
            del definitions[target_var]
        if target_var in composed_definitions.keys():
            del composed_definitions[target_var]
    return target_variables


##########################################################################################
### inline variable definitions
##########################################################################################

def inline_variable_definitions(smt_encoding):
    # Only inline if var not in excluded list
    for var, def_expr in reversed(list(definitions.items())):
        if var in target_variables:
            continue
        # Replace the variable to its definition
        escaped_var = re.escape(var)
        smt_encoding = re.sub(escaped_var, def_expr, smt_encoding)
    return smt_encoding

##########################################################################################
### extract assert expressions
##########################################################################################
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


##########################################################################################
### expand let expressions
##########################################################################################
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


def process_smt_encoding(smt_path, defs_path, target_vars_path, output_path):
    # Load inputs
    parse_variable_definitions(defs_path)
    load_target_variables(target_vars_path)
    simplify_variable_definitions()

    with open(smt_path, 'r', encoding='utf-8') as f:
        smt_encoding = f.read()
        smt_lines = smt_encoding.splitlines()

    inlined_smt_encoding = inline_variable_definitions(smt_encoding)
    inlined_smt_lines = inlined_smt_encoding.splitlines()
    
    assert_exprs = extract_assert_expressions(inlined_smt_lines)
    assert_exprs = expand_let_expressions(assert_exprs)

    with open(output_path, 'w', encoding='utf-8') as f:
        for expr in assert_exprs:
            f.write(expr + '\n')

    print(f"Inlined SMT encoding written to {output_path}")


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: python inlining_equals_variables.py /your/path/to/work/directory")
        exit(1)

    path = sys.argv[1]
    smt_encoding_file = os.path.join(path, 'smt_encoding.smt2')
    equal_definitions_file = os.path.join(path, 'filtered_equal_definitions.txt')
    target_variables_file = os.path.join(path, 'target_variables.txt')
    output_inlined_file = os.path.join(path, 'inlined_smt_encoding.smt2')

    process_smt_encoding(smt_encoding_file, equal_definitions_file, target_variables_file, output_inlined_file)
