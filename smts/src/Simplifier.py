from typing import List, Union

class ExprNode:
    def __init__(self, op: str, args: List[Union['ExprNode', str]]):
        self.op = op  # e.g., 'ite', '=', 'and', 'or', 'not', 'var', 'const'
        self.args = args  # children

    def __repr__(self):
        return f"({self.op} {' '.join(map(str, self.args))})"

class Condition:
    def __init__(self, clauses=None):
        self.clauses = clauses if clauses is not None else []

    def add(self, clause: ExprNode):
        self.clauses.append(clause)

    def __repr__(self):
        return " ∧ ".join(map(str, self.clauses))

class Equality:
    def __init__(self, var: str, value: ExprNode, condition: Condition):
        self.var = var
        self.value = value
        self.condition = condition

    def __repr__(self):
        return f"{self.var} = {self.value}  if  ({self.condition})"

class EqualityExtractor:
    def extract(self, expr: ExprNode, condition: Condition = None) -> List[Equality]:
        condition = condition or Condition()

        # Simplest case: (= x expr)
        if expr.op == '=' and isinstance(expr.args[0], str):
            return [Equality(expr.args[0], expr.args[1], condition)]

        # ITE 表达式：需要递归两边
        if expr.op == 'ite':
            cond_expr, true_branch, false_branch = expr.args
            cond_true = Condition(condition.clauses + [cond_expr])
            cond_false = Condition(condition.clauses + [ExprNode('not', [cond_expr])])
            return self.extract(true_branch, cond_true) + self.extract(false_branch, cond_false)

        # 其他结构（暂不提取）
        return []

class EqualityPropagator:
    def __init__(self, equalities: List[Equality]):
        self.eq_map = {eq.var: eq.value for eq in equalities}

    def substitute(self, expr: ExprNode) -> ExprNode:
        if isinstance(expr, str):
            return expr
    
        if expr.op == 'var' and expr.args[0] in self.eq_map:
            return self.eq_map[expr.args[0]]
    
        # === ITE 特殊处理 ===
        if expr.op == 'ite':
            cond = self.substitute(expr.args[0])
            true_branch = self.substitute(expr.args[1])
            false_branch = self.substitute(expr.args[2])
    
            # 判断条件表达式是否恒为真或假
            if isinstance(cond, ExprNode) and cond.op == '=':
                lhs, rhs = cond.args
                if lhs == rhs:
                    return true_branch
                # 支持 cond 变成具体值，如 h = #b00，而我们知道 h = #b00
                if lhs in self.eq_map and self.eq_map[lhs] == rhs:
                    return true_branch
                if lhs in self.eq_map and self.eq_map[lhs] != rhs:
                    return false_branch
    
            if isinstance(cond, str) and cond == 'true':
                return true_branch
            if isinstance(cond, str) and cond == 'false':
                return false_branch
    
            # 无法简化就保留 ITE
            return ExprNode('ite', [cond, true_branch, false_branch])
    
        # 普通表达式继续递归替换
        return ExprNode(expr.op, [
            self.substitute(arg) if isinstance(arg, ExprNode) else arg
            for arg in expr.args
        ])

class Simplifier:
    def __init__(self, expressions: List[ExprNode]):
        self.expressions = expressions
        self.known_equalities = []

    def run(self):
        changed = True
        seen_exprs = set()

        while changed:
            changed = False
            extractor = EqualityExtractor()
            propagator = EqualityPropagator(self.known_equalities)

            for expr in self.expressions:
                expr_str = repr(expr)
                if expr_str in seen_exprs:
                    continue  # 防止死循环
                seen_exprs.add(expr_str)

                substituted_expr = propagator.substitute(expr)
                new_equalities = extractor.extract(substituted_expr)

                for eq in new_equalities:
                    if eq.var not in [e.var for e in self.known_equalities]:
                        self.known_equalities.append(eq)
                        changed = True

        return self.known_equalities

if __name__ == "__main__":    
    # x = (ite (= h #b00) 5 0)
    expr1 = ExprNode('=', [
        'x',
        ExprNode('ite', [
            ExprNode('=', ['h', '#b00']),
            ExprNode('const', ['5']),
            ExprNode('const', ['0'])
        ])
    ])
    # h = #b00
    expr2 = ExprNode('=', ['h', '#b00'])
    
    simplifier = Simplifier([expr2, expr1])
    results = simplifier.run()

    for eq in results:
        print(eq)
