import argparse
import re
import subprocess
from pathlib import Path
from z3 import *

"""
def extract_target_vars(con_file):
    # Extract target variables 'Config_' from the configs_to_variables file
    lines = Path(con_file).read_text().splitlines()
    target_vars = []
    for line in lines:
        line = line.strip()
        if line.startswith("+ Config_"):
            target_vars.append(line[2:].strip())  # remove "+ "
    return target_vars
"""

def extract_target_vars(con_file):
    """ Extract target variables 'Config_' from the config_constraints file """
    declare_re = re.compile(
        r'\(declare-fun\s+(Config[^\s]*)\s*\(\)\s*'
        r'((\(_\s+BitVec\s+(\d+)\))|(Int|Bool))\)',
        re.DOTALL
    )
    target_vars = []

    with open(con_file, 'r') as f:
        content = f.read()
        matches = declare_re.findall(content)

        for match in matches:
            var_name = match[0]
            if match[4] in ['Int', 'Bool']:  # Int or Bool
                var_type = match[4]
            else:  # BitVec
                var_type = 'BitVec'
            target_vars.append((var_name, var_type))

    return target_vars

def ensure_directory_exists(output_dir):
    """Ensure the output directory exists, if not, create it."""
    Path(output_dir).mkdir(parents=True, exist_ok=True)

def comment_asserts_with_var(lines, target_var, output_dir):
    # Ensure the output directory exists
    ensure_directory_exists(output_dir)

    # Comment out assert expressions that involve the target variable
    pattern = re.compile(r"\(assert\s+(?:\(=|\(not)?\s*" + re.escape(target_var) + r"\b")
    modified = []
    buffer = []
    inside = False
    matched = False  # a flag to indicate if the variable was matched

    for line in lines:
        if inside:
            buffer.append(";" + line)
            if ")" in line:
                inside = False
                modified.extend(buffer)
                buffer = []
        elif pattern.search(line):
            matched = True
            inside = True
            buffer = [";" + line]
            if ")" in line:
                inside = False
                modified.extend(buffer)
                buffer = []
        else:
            modified.append(line)

    if not matched:
        print(f"\033[93m[WARN] {target_var} not found in file\033[0m")
    else:
        modified_path = Path(output_dir) / f"{target_var}.smt2"
        modified_path.parent.mkdir(parents=True, exist_ok=True)  # Create parent directories if they don't exist
        with open(modified_path, 'w') as mf:
            mf.writelines(modified)

    return modified

def run_z3_on_temp_file(lines):
    with open("temp_modified.smt2", "w") as f:
        f.writelines(lines)
    try:
        res = subprocess.run(["z3", "temp_modified.smt2"], capture_output=True, text=True, timeout=10)
        return res.stdout.strip()
    except Exception as e:
        return f"Error: {e}"

def process_all_targets_unsat(smt_file, con_file, result_file, output_dir):
    lines = Path(smt_file).read_text().splitlines(keepends=True)
    targets = extract_target_vars(con_file)

    for var, _ in targets:
        print(f"\033[0m[Checking] {var} ...\033[0m")
        modified = comment_asserts_with_var(lines, var, output_dir)
        result = run_z3_on_temp_file(modified)

        if "unsat" not in result:
            with open(result_file, 'a') as rf:
                rf.write(var + '\n')
            print(f"\033[92m[SAT] {var}\033[0m")
        else:
            print(f"\033[90m[UNSAT] {var}\033[0m")

def process_all_targets_sat(smt_file, con_file, result_file, output_dir):
    lines = Path(smt_file).read_text().splitlines(keepends=True)
    targets = extract_target_vars(con_file)

    for var, var_type in targets:
        print(f"\033[0m[Checking] {var} ...\033[0m")
        # modified = comment_asserts_with_var(lines, var, output_dir)
        comment_asserts_with_var(lines, var, output_dir)

        # === Step 1: Load SMT2 and parse whole file ===
        with open(Path(output_dir) / f"{var}.smt2", "r") as f:
            smt_content = f.read()
        
        try:
            a_ast = parse_smt2_string(smt_content)
        except Exception as e:
            print(f"[ERROR] Failed to parse SMT2 file: {e}")
            exit(1)
        
        # === Step 2: Create solver and extract constraints ===
        s = Solver()
        a_ctx = [expr for expr in a_ast]
        
        # === Step 3: Wrap all constraints into one formula A_formula ===
        # A_formula = Bool("A_formula")
        # s.add(A_formula == And(a_ctx))
        
        # === Step 4: Create quantified variable ===
        if var_type == "BitVec":
            config_var = BitVec(var, 32)
        elif var_type == "Int":
            config_var = Int(var)
        elif var_type == "Bool":
            config_var = Bool(var)
        else:
            raise ValueError(f"Unsupported config_var_type: {config_var_type}")
        
        # === Step 5: Add universal quantifier (network invariant) ===
        s.push()
        # s.add(ForAll([config_var], A_formula))
        s.add(ForAll([config_var], And(a_ctx)))
        
        # === Step 6: Check ===
        result = s.check()
        if sat == result:
            print(f"\033[90m[SAT] {var}\033[0m")
        else:
            with open(result_file, 'a') as rf:
                rf.write(var + '\n')
            print(f"\033[92m[UNSAT] {var}\033[0m")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("dir", default=".", help="Working directory (default: current)")
    parser.add_argument("-s", "--status", choices=["unsat", "sat"], default="unsat",
                        help="Only output UNSAT (default) or SAT variables")

    args = parser.parse_args()

    base = Path(args.dir)
    smt_file = base / "smt_encoding.smt2"
    con_file = base / "config_constraints.smt2"
    result_file = base / "key_variables.txt"
    output_dir = base / "commented_one_config_constraint"

    if args.status == "unsat":
        process_all_targets_unsat(smt_file, con_file, result_file, output_dir)
    else:
        process_all_targets_sat(smt_file, con_file, result_file, output_dir)
