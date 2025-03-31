from z3 import *

def get_vars(expr):
    """Return all uninterpreted variables in expr"""
    seen = set()
    def _visit(e):
        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
            seen.add(e)
        for child in e.children():
            _visit(child)
    _visit(expr)
    return seen

def find_assertions_with_var(var, assertions):
    """Find all assertions that mention this variable"""
    relevant = []
    for a in assertions:
        for v in get_vars(a):
            if v.decl() == var.decl():
                relevant.append(a)
                break
    return relevant

def show_dependency_layer(var, assertions):
    """Print one layer of dependencies for a given variable"""
    print(f"\n📌 {var} appears in:")
    relevant_asserts = find_assertions_with_var(var, assertions)
    if not relevant_asserts:
        print("  (no assertions)")
        return set()

    next_vars = set()
    for a in relevant_asserts:
        print(f"  - {a}")
        for dep in get_vars(a):
            if dep.decl() != var.decl():
                next_vars.add(dep)

    # if next_vars:
        # print(f"🧠 Variables related to {var}: " + ", ".join(str(v) for v in next_vars))
    return next_vars

def interactive_trace(assertions, all_vars):
    visited = set()
    while True:
        var_name = input("\n🔎 Enter a variable (or 'exit'): ").strip()
        if var_name.lower() == 'exit':
            break
        if var_name not in all_vars:
            print(f"❌ Variable '{var_name}' not found.")
            continue
        var = all_vars[var_name]
        if var in visited:
            print("  (already visited)")
            continue
        visited.add(var)
        related = show_dependency_layer(var, assertions)

def main():
    import sys
    if len(sys.argv) != 2:
        print("Usage: python interactive_dependency_tracer.py <file.smt2>")
        return

    file_path = sys.argv[1]

    solver = Solver()
    with open(file_path, 'r') as f:
        smt2_str = f.read()
        solver.from_string(smt2_str)

    assertions = solver.assertions()
    all_vars = {v.decl().name(): v for a in assertions for v in get_vars(a)}

    print("✅ Loaded SMT file.")
    print(f"Available variables: {', '.join(all_vars.keys())}")
    interactive_trace(assertions, all_vars)

if __name__ == "__main__":
    main()
