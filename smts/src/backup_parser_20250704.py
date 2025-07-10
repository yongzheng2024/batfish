from typing import Dict, List, Union, Optional


class CondNode:
    def __init__(self, cond_expr, cond_value, equal_exprs, expr_id):
        """
        Represents a conditional node extracted from an SMT expression.

        Args:
            expr_id: int — index of the source SMT expression
            cond_expr: condition expression (ExprNode or string)
            cond_value: True or False
            equal_exprs: Dict[str, ExprNode] — target var and their definition under this condition
        """
        self.expr_id = expr_id
        self.cond_expr = cond_expr
        self.cond_value = cond_value
        self.equal_exprs = equal_exprs

    def __repr__(self):
        return (f"CondNode(expr_id={self.expr_id}, cond={self.cond_expr}, "
                f"value={self.cond_value}, equal_exprs={self.equal_exprs})")

class ExprNode:
    def __init__(self, op, args):
        """
        Represents a node in the expression tree (AST) for SMT formulas.

        Args:
            op (str):
                The operator for this expression, e.g., 'ite', '=>', '=', 
                'or', 'and', 'not', 'bvule', 'extract', 'const', 'var'.
            args (List[Union[ExprNode, str]]):
                Arguments for the operator. These can be nested ExprNode instances 
                or strings (for constants or variable names).
        """
        self.op = op
        self.args = args

    def __repr__(self):
        return f"({self.op} {' '.join(str(a) for a in self.args)})"


def parse(expr: ExprNode) -> list[CondNode]:
    cond_nodes = []

    if expr.op == 'ite':
        cond = expr.args[0]
        true_branch = expr.args[1]
        false_branch = expr.args[2]

        cond_nodes += handle_branch(cond, True, true_branch)
        cond_nodes += handle_branch(cond, False, false_branch)

    elif expr.op == '=>':
        cond = expr.args[0]
        conclusion = expr.args[1]
        # p => q  等价于  not p or q
        cond_nodes += handle_branch(cond, True, conclusion)

    elif expr.op == 'or':
        for arg in expr.args:
            cond_nodes += handle_branch(arg, True, ExprNode('true_expr', []))

    elif expr.op == 'and':
        for arg in expr.args:
            cond_nodes += parse_expr_to_condnodes(arg)

    elif expr.op == '=':
        left, right = expr.args
        # left 是 variable 名
        if isinstance(left, str):
            cond_nodes.append(CondNode(cond_expr=None, cond_value=None, equal_exprs={left: right}))
        else:
            cond_nodes.append(CondNode(cond_expr=None, cond_value=None, equal_exprs={"(complex)": expr}))

    else:
        # fallback to default equality
        cond_nodes.append(CondNode(cond_expr=None, cond_value=None, equal_exprs={"(unknown)": expr}))

    return cond_nodes


def parse_ite_expr_to_cond_nodes(expr: ExprNode, expr_id: int) -> list[CondNode]:
    """
    Parse an (ite cond then else) expression into multiple CondNode objects.
    """
    assert expr.op == 'ite' and len(expr.args) == 3, "Must be an ITE expression"

    cond, then_expr, else_expr = expr.args

    cond_nodes = []

    # Simplify THEN branch
    then_equal_exprs = extract_equal_exprs(then_expr)

    # Create one node for the full condition being true
    cond_nodes.append(CondNode(
        cond_expr=cond,
        cond_value=True,
        equal_exprs=then_equal_exprs,
        expr_id=expr_id
    ))

    # Create fallback CondNodes if cond is an 'and' expression
    if isinstance(cond, ExprNode) and cond.op == 'and':
        for subcond in cond.args:
            fallback_equal_exprs = extract_equal_exprs(else_expr)
            cond_nodes.append(CondNode(
                cond_expr=subcond,
                cond_value=False,
                equal_exprs=fallback_equal_exprs,
                expr_id=expr_id
            ))

    return cond_nodes

def extract_equal_exprs(expr: ExprNode) -> Dict[str, ExprNode]:
    """
    Given an expression like (and (= v1 val1) (= v2 val2) ...)
    return a dictionary {v1: val1, v2: val2, ...}
    """
    if expr.op == 'and':
        exprs = expr.args
    else:
        exprs = [expr]

    equal_map = {}
    for e in exprs:
        if isinstance(e, ExprNode) and e.op == '=' and isinstance(e.args[0], str):
            equal_map[e.args[0]] = e.args[1] if len(e.args) > 1 else None
    return equal_map


def handle_branch(cond_expr: ExprNode, cond_value: bool, branch_expr: ExprNode) -> list[CondNode]:
    """
    从某个条件（True 或 False 分支）中提取 equality 表达式
    """
    branch_nodes = parse(branch_expr)

    for node in branch_nodes:
        if node.cond_expr is None:
            node.cond_expr = cond_expr
            node.cond_value = cond_value
        else:
            # 合并条件（嵌套）
            node.cond_expr = ExprNode('and', [
                ExprNode('cond', [cond_expr, cond_value]),
                node.cond_expr
            ])
    return branch_nodes

if __name__ == "__main__":
    ite_expr = ExprNode('ite', [
        ExprNode('and', [
            ExprNode('=', ['e1', 'c1']),
            ExprNode('=', ['e2', 'c2']),
            ExprNode('=', ['e3', 'c3'])
        ]),
        ExprNode('and', [
            'v1',
            ExprNode('=', ['v2', 'c4'])
        ]),
        ExprNode('not', ['v1'])
    ])
    
    cond_nodes = parse_ite_expr_to_cond_nodes(ite_expr, expr_id=0)
    for node in cond_nodes:
        print(node)
