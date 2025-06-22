import os
import re
import sys


##########################################################################################
### SMT2 variable regex and constant regex
### SMT2 assert experssions
##########################################################################################

# SMT2 variable regex (supports quoted identifiers (|...|) and normal indentifiers)
var_regex =   r'(\|[^|]*?(?:\\\|[^|]*?)*\||[^\s()]+)'
# SMT2 constant regex (supports #xabc12345 and 25)
const_regex = r'(#[xX][0-9a-fA-F]+|\d+)'

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


##########################################################################################
### parse variable definitions (involving intermediate and configuration variable)
##########################################################################################

def parse_intermediate_definitions(file_path):
    definitions = {}
    current_var = None
    cached_definitions = set()

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
        # print("88888888888888888888888888888888888888888888888888888888")
        if rhs_var not in definitions:
            definitions[rhs_var] = definitions[lhs_var]
        if lhs_var not in definitions:
            definitions[lhs_var] = definitions[rhs_var]

    with open(file_path, 'r') as f:
        lines = [line.strip() for line in f if line.strip()]

    i = 0
    while i < len(lines):
        line = lines[i]
        # print(line)

        # Match var ending with colon (includes escaped characters safely)
        if not line.endswith(':'):
            error_invalid_expr(line)
            i += 1
            continue

        current_var = line.rstrip(':')
        i += 1
        if i >= len(lines):
            break

        current_defs = set()
        while i < len(lines) and not lines[i].strip().endswith(':'):
            current_defs.add(lines[i])
            i += 1

        if len(current_defs) == 2:
            handle_multi_exprs(current_var, list(current_defs))
            continue
        elif len(current_defs) > 2:
            # TODO: implement more handle methods for multiple expressions
            # print error information (and exit)
            error_multi_exprs(current_var, current_defs)
            exit(1)

        # Normal: a variable has only one corresponding definition
        def_line = list(current_defs)[0]

        # Scenario 0
        if (eqvc := extract_assert_eqvc(def_line)):
            # print("00000000000000000000000000000000000000000000000000000000")
            left, right = eqvc
            if left == current_var:
                definitions[current_var] = right
                continue

        # Scenario 1
        if (eqvv := extract_assert_eqvv(def_line)):
            # print("11111111111111111111111111111111111111111111111111111111")
            cached_definitions.add(def_line)

        # Scenario 2
        if (eqve := extract_assert_eqve(def_line)):
            # print("22222222222222222222222222222222222222222222222222222222")
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
            # print("33333333333333333333333333333333333333333333333333333333")
            definitions[current_var] = "false"
            continue

        # Scenario 4
        if (true_var := extract_assert_true(def_line)):
            if (true_var != current_var):
                error_invalid_expr(def_line)
                exit(1)
            # print("44444444444444444444444444444444444444444444444444444444")
            definitions[current_var] = "true"
            continue

        # Scenario 5, TODO
        for left, right in extract_assert_ands(def_line):
            if left == current_var:
                # print("55555555555555555555555555555555555555555555555555555555")
                definitions[current_var] = right
                break
            elif right == current_var:
                # print("55555555555555555555555555555555555555555555555555555555")
                definitions[current_var] = left
                break

    # Scenario 1
    for def_line in list(cached_definitions):
        if (eqvv := extract_assert_eqvv(def_line)):
            # print("11111111111111111111111111111111111111111111111111111111")
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
                error_equal_variables_diff(def_line)
                print(f"{lhs_var}: {definitions[lhs_var]}")
                print(f"{rhs_var}: {definitions[rhs_var]}")
                exit(1)

    return definitions


def load_excluded_vars(path):
    with open(path, 'r') as f:
        return set(line.strip() for line in f if line.strip())


def inline_definitions(smt_content, definitions, excluded_vars):
    # Only inline if var not in excluded list
    for var, val in definitions.items():
        if var not in excluded_vars:
            # Replace whole word (SMT identifiers)
            pattern = rf'(?<![\w|]){re.escape(var)}(?![\w|])'
            smt_content = re.sub(pattern, f'({val})', smt_content)
    return smt_content


def process_smt_encoding(smt_path, defs_path, target_vars_path, output_path):
    # Load inputs
    definitions = parse_intermediate_definitions(defs_path)
    # print(definitions)

    """
    excluded_vars = load_excluded_vars(target_vars_path)

    with open(smt_path, 'r') as f:
        content = f.read()

    simplified_content = inline_definitions(content, definitions, excluded_vars)

    with open(output_path, 'w') as f:
        f.write(simplified_content)

    print(f"Simplified SMT written to {output_path}")
    """


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: python inlining_equals_variables.py /your/path/to/work/directory")
        exit(1)

    path = sys.argv[1]
    smt_encoding_file = os.path.join(path, 'smt_encoding.smt2')
    equals_variable_file = os.path.join(path, 'filtered_equals_variable.txt')
    target_variable_file = os.path.join(path, 'target_variable.txt')
    output_inlined_file = os.path.join(path, 'inlined_smt_encoding.smt2')

    process_smt_encoding(smt_encoding_file, equals_variable_file, target_variable_file, output_inlined_file)
