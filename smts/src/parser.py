
from typing import List, Dict, Union
from dataclasses import dataclass

@dataclass
class ExprNode:
    """
    Represents a symbolic expression node in the SMT expression tree.

    Attributes:
        op: The operator string (e.g., 'ite', 'bvule', '=', 'extract', 'const', 'var', etc.).
        args: The arguments of the expression. Each argument can be a string or another ExprNode.
    """
    def __init__(self, op: str, args: List[Union['ExprNode', str]]):
        self.op = op
        self.args = args

    def __repr__(self):
        return f"({self.op} {' '.join(str(a) for a in self.args)})"

    def is_var(self) -> bool:
        return self.op == "var"

    def is_const(self) -> bool:
        return self.op == "const"

def make_var(name: str) -> ExprNode:
    """Create a variable node."""
    return ExprNode("var", [name])

def make_const(val: str) -> ExprNode:
    """Create a constant node."""
    return ExprNode("const", [val])

@dataclass
class CondNode:
    """
    Represents a conditional definition of variable expressions under certain branch conditions.

    Attributes:
        cond_expr: The condition under which this node applies (can be an ExprNode, str, etc.).
        cond_value: True or False — whether the condition should evaluate to True or False.
        equal_exprs: A mapping from variable name (str) to its ExprNode expression under this condition.
        expr_id: An optional identifier (e.g., index of the originating expression in the assertion list).
    """
    def __init__(self, cond_expr, cond_value: bool, equal_exprs: Dict[str, ExprNode], expr_id: int = -1):
        self.cond_expr = cond_expr
        self.cond_value = cond_value
        self.equal_exprs = equal_exprs
        self.expr_id = expr_id

    def __repr__(self):
        return (
            f"CondNode(\n"
            f"  cond_expr={self.cond_expr},\n"
            f"  cond_value={self.cond_value},\n"
            f"  equal_exprs={self.equal_exprs},\n"
            f"  expr_id={self.expr_id})"
        )

# ==================== Parsing Framework ====================

class CondNodeExtractor:
    def __init__(self):
        self.cond_nodes: List[CondNode] = []

    def parse_all(self, expressions: List[ExprNode]) -> List[CondNode]:
        for idx, expr in enumerate(expressions):
            self.parse_top_expr(expr, idx)
        return self.cond_nodes

    def parse_top_expr(self, expr: ExprNode, expr_id: int):
        if expr.op == 'ite':
            self.handle_ite(expr, expr_id)
        elif expr.op == '=':
            self.handle_equal(expr, expr_id)
        else:
            # TODO: extend to other top-level operators like =>, assert, etc.
            print(f"[Warn] Unhandled top-level op: {expr.op}")

    def handle_ite(self, expr: ExprNode, expr_id: int):
        cond_expr, then_expr, else_expr = expr.args
        if cond_expr.op == 'and':
            # then-branch
            and_node = CondNode(cond_expr, True, self.extract_equal_exprs(then_expr), expr_id)
            self.cond_nodes.append(and_node)
            for sub in cond_expr.args:
                false_node = CondNode(sub, False, self.extract_equal_exprs(else_expr), expr_id)
                self.cond_nodes.append(false_node)
        elif cond_expr.op == 'or':
            # else-branch
            or_node = CondNode(cond_expr, False, self.extract_equal_exprs(else_expr), expr_id)
            self.cond_nodes.append(or_node)
            for sub in cond_expr.args:
                true_node = CondNode(sub, True, self.extract_equal_exprs(then_expr), expr_id)
                self.cond_nodes.append(true_node)
        else:
            # normal ite condition
            cond_true = CondNode(cond_expr, True, self.extract_equal_exprs(then_expr), expr_id)
            cond_false = CondNode(cond_expr, False, self.extract_equal_exprs(else_expr), expr_id)
            self.cond_nodes.append(cond_true)
            self.cond_nodes.append(cond_false)

    def handle_equal(self, expr: ExprNode, expr_id: int):
        # Example: (= x some_expr)
        lhs, rhs = expr.args
        if isinstance(lhs, str):  # left side is variable
            node = CondNode(cond_expr='True', cond_value=True, equal_exprs={lhs: rhs}, expr_id=expr_id)
            self.cond_nodes.append(node)

    def extract_equal_exprs(self, expr: Union[ExprNode, str]) -> Dict[str, ExprNode]:
        result = {}
    
        if isinstance(expr, str):
            # 直接是一个变量名，视为变量 = true
            result[expr] = ExprNode('const', ['true'])
            return result
    
        if expr.op == 'and':
            for sub in expr.args:
                result.update(self.extract_equal_exprs(sub))
        elif expr.op == '=':
            lhs, rhs = expr.args
            if isinstance(lhs, str):
                result[lhs] = rhs
        elif expr.op == 'not':
            sub = expr.args[0]
            if isinstance(sub, str):
                result[sub] = ExprNode('const', ['false'])
    
        return result


if __name__ == "__main__":
    # EXPR:
    # (ite (and (= e1 c1) (= e2 c2)) (and v1 (= v2 c3)) (not v1))
    expr = ExprNode('ite', [
        ExprNode('and', [
            ExprNode('=', ['e1', 'c1']),
            ExprNode('=', ['e2', 'c2'])
        ]),
        ExprNode('and', [
            'v1',
            ExprNode('=', ['v2', 'c3'])
        ]),
        ExprNode('not', ['v1'])
    ])

    extractor = CondNodeExtractor()
    nodes = extractor.parse_all([expr])
    for n in nodes:
        print(n)
