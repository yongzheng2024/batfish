import os
import re
import sys

# SMT2 variable regex (supports quoted identifiers (|...|) and normal indentifiers)
variable_pattern = r'(\|[^|]*?(?:\\\|[^|]*?)*\||[^\s()]+)'
compiled_variable_patterntern = re.compile(variable_pattern)

def smt_var_equal(a, b):
    return a.strip() == b.strip()

def parse_intermediate_definitions(file_path):
    definitions = {}
    current_var = None

    def extract_assert_eq(expr):
        # Matches: (assert (= X Y)) where X or Y can be complex expressions
        match = re.match(rf'^\(assert\s+\(=\s+{variable_pattern}\s+(.+)\)\)$', expr)
        if match:
            return match.groups();
        match = re.match(rf'^\(assert\s+\(=\s+(.+)\s+{variable_pattern}\)\)$', expr)
        if match:
            return match.groups();
        return None

    def extract_not(expr):
        match = re.match(r'\(assert\s+\(not\s+{variable_pattern}\)\)', expr)
        return match.group(1) if match else None

    def extract_assert(expr):
        match = re.match(r'\(assert\s+{variable_pattern}\)', expr)
        return match.group(1) if match else None

    def extract_and_eq(expr):
        and_match = re.match(r'\(assert\s+\(and\s+(.*)\)\)', expr)
        if and_match:
            inner = and_match.group(1)
            return re.findall(r'\(=\s+(.+?)\s+(.+?)\)', inner)
        return []

    with open(file_path, 'r') as f:
        lines = [line.strip() for line in f if line.strip()]

    i = 0
    while i < len(lines):
        line = lines[i]

        # Match var ending with colon (includes escaped characters safely)
        if line.endswith(':'):
            current_var = line.rstrip(':')
            i += 1
            if i >= len(lines):
                break

            current_defs = set()
            while i < len(lines) and not lines[i].strip().endswith(':'):
                current_defs.add(lines[i])
                i += 1

            # TODO: firstly, you should check the current_defs have non-copy defs
            # if it have non-copy defs, print current_var and all defs, and exit(1)
            if len(current_defs) > 1:
                print(f"ERROR: {current_var} has multiple definitions:")
                for current_def in current_defs:
                    print(current_def)

            def_line = list(current_defs)[0]

            # Scenario 1 & 2
            eq = extract_assert_eq(def_line)
            if eq:
                left, right = eq
                if left == current_var:
                    definitions[current_var] = right
                    i += 1
                    continue
                elif right == current_var:
                    definitions[current_var] = left
                    i += 1
                    continue
                else:
                    print(def_line)
                    print(left)
                    print(right)
                    print(current_var)

            # Scenario 3
            simple = extract_assert(def_line)
            if simple == current_var:
                definitions[current_var] = "true"
                i += 1
                continue

            # Scenario 4
            not_var = extract_not(def_line)
            if not_var == current_var:
                definitions[current_var] = "false"
                i += 1
                continue

            # Scenario 5
            for left, right in extract_and_eq(def_line):
                if left == current_var:
                    definitions[current_var] = right
                    break
                elif right == current_var:
                    definitions[current_var] = left
                    break

            i += 1
        else:
            i += 1

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
    print(definitions)
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
