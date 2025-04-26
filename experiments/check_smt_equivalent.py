from z3 import *
import argparse
from z3 import *

# Add a command-line argument parser
parser = argparse.ArgumentParser(description="Check logical equivalence of SMT encodings.")
parser.add_argument("dir", default=".", help="Path to the work directory")
args = parser.parse_args()

#Construct paths to the three SMT files using the given directory
SMT_OUTPUT_DIRECTORY = args.dir
SMT_ENCODING1_FILE = SMT_OUTPUT_DIRECTORY + "/smt_encoding.smt2"
SMT_ENCODING2_FILE = SMT_OUTPUT_DIRECTORY + "/smt_encoding_original.smt2"
SMT_CONSTRAINTS_FILE = SMT_OUTPUT_DIRECTORY + "/config_constraints.smt2"

# Load SMT2 files
with open(SMT_ENCODING1_FILE, "r") as f:
    a_ast = parse_smt2_string(f.read())

with open(SMT_ENCODING2_FILE, "r") as f:
    b_ast = parse_smt2_string(f.read())

with open(SMT_CONSTRAINTS_FILE, "r") as f:
    c_ast = parse_smt2_string(f.read())

# Create a fresh solver
s = Solver()

# Add declarations and constraints from both files in isolated environments
a_ctx = []
b_ctx = []
c_ctx = []

# We assume shared declarations (variables used in both files) are the same

# Separate the constraints from the ASTs
for expr in a_ast:
    a_ctx.append(expr)
for expr in b_ast:
    b_ctx.append(expr)
for expr in c_ast:
    c_ctx.append(expr)

# Create boolean formulas for A and B
A_formula = Bool("A_formula")
B_formula = Bool("B_formula")

# Create constraints
Constraints = Bool("Constraints")

# Wrap A and B formulas using "let-style" constructs
s.add(A_formula == And(a_ctx))
s.add(B_formula == And(b_ctx))
s.add(Constraints == And(c_ctx))

# Now check if the two formulas are NOT equal (i.e., check for logical difference)
s.push()
s.add(Not(Implies(Constraints, A_formula == B_formula)))
result = s.check()

# Print result
# print(result)
if result == unsat:
    print("✅ The two SMT encodings are logically equivalent.")
else:
    print("❌ The two SMT encodings are NOT logically equivalent.")
    # print("Model showing difference:")
    # print(s.model())
