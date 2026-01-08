import ast
from typing import TypeGuard, Literal, Protocol, TypeVar, Iterable

from pymcl import r as ρ

from .types import Fld, Var, Gal, Getw, Args
from .circuit import Circuit, Bin, Set, Dat


T = TypeVar("T")


class Callable(Protocol[T]):
    def __call__(self, *args: T) -> T: ...


All = Dat | Set | str | None | tuple["All", ...] | Callable["All"]
Tag = tuple[Literal["continue"], None] | tuple[Literal["break"], None] | tuple[Literal["return"], All] | tuple[None, None]


# check the type of a value

def isgal(x: All) -> TypeGuard[Gal]:
    return isinstance(x, Fld | Var)


def isbin(x: All) -> TypeGuard[Bin]:
    return isinstance(x, list) and all(isinstance(b, Fld | Var) for b in x)


# assert the type of a value

def asgal(x: All) -> Gal:
    if isinstance(x, Fld | Var):
        return x
    raise TypeError("expected a field element")


def asbin(x: All) -> Bin:
    if isinstance(x, list) and all(isinstance(b, Fld | Var) for b in x):
        return x
    raise TypeError("expected a binary value")


def aslof(x: All) -> list[Gal]:
    if isinstance(x, list) and all(isinstance(v, Fld | Var) for v in x):
        return x
    raise TypeError("expected a list of field elements")


def asstr(x: All) -> str:
    if isinstance(x, str):
        return x
    raise TypeError("expected a string")


def asint(x: All, sgn: bool = True, nat: bool = False) -> Fld:
    if isinstance(x, int) and (not sgn or (x := (x + (ρ - 1) // 2) % ρ - (ρ - 1) // 2) >= 0 or not nat):
        return x
    raise TypeError("expected a {} constant field element".format("non-negative" if nat else "signed" if sgn else "unsigned"))


# get the shape of a value (binary value will be treated as a list of field elements)


RecursiveShape = tuple[Literal["gal"], None] | tuple[Literal["any"], None] | tuple[Literal["tup"], tuple["RecursiveShape", ...]] | tuple[Set, "RecursiveShape"]


def recursive_shape(x: All) -> RecursiveShape:
    if isinstance(x, Fld | Var):
        return "gal", None
    if isinstance(x, tuple):
        return "tup", tuple(recursive_shape(v) for v in x)
    if isinstance(x, list):
        shapes = {recursive_shape(v) for v in x}
        assert len(shapes) <= 1
        return range(len(x)), shapes.pop() if shapes else ("any", None)
    if isinstance(x, dict):
        shapes = {recursive_shape(v) for v in x.values()}
        assert len(shapes) <= 1
        return frozenset(x), shapes.pop() if shapes else ("any", None)
    raise TypeError("unsupported data type")


# built-in functions


def xxzip(fst: All, *args: All) -> All:
    if isinstance(fst, list):
        if not all(isinstance(arg, list) and range(len(fst)) == range(len(arg)) for arg in args):
            raise TypeError("inconsistent shape of zipped arguments")
        return [(fst[key], *(arg[key] for arg in args)) for key in range(len(fst))]
    if isinstance(fst, dict):
        if not all(isinstance(arg, dict) and frozenset(fst) == frozenset(arg) for arg in args):
            raise TypeError("inconsistent shape of zipped arguments")
        return {key: (fst[key], *(arg[key] for arg in args)) for key in frozenset(fst)}
    raise TypeError("only lists and dicts are supported for zipping")


def xxcon(*args: All) -> All:
    shapes = [recursive_shape(arg) for arg in args]
    if not all(isinstance(keys, range) for keys, inner in shapes):
        raise TypeError("only lists are supported for concatenation")
    if len({inner for keys, inner in shapes if inner != ("any", None)}) > 1:
        raise TypeError("inconsistent shape of concatenated arguments")
    return sum(args, [])


def xxrep(arg: All, n: All) -> All:
    if isinstance(arg, list):
        return arg * asint(n, nat=True)
    raise TypeError("only lists are supported for repetition")


def xxslc(arg: All, i: All, j: All) -> All:
    if isinstance(arg, list):
        i = asint(i) % len(arg)
        j = asint(j) % len(arg)
        return arg[i:j] if i < j else arg[i:] + arg[:j]
    raise TypeError("only lists are supported for slicing")


def xxrev(arg: All) -> All:
    if isinstance(arg, list):
        return arg[::-1]
    raise TypeError("only lists are supported for reversing")


def xxlen(arg: All) -> All:
    if isinstance(arg, list):
        return len(arg)
    raise TypeError("only lists are supported for getting length")


class Program(Circuit, ast.NodeVisitor):
    # The Compiler class is a wrapper of the Circuit class, it compiles the given Python code to the
    # arithmetic circuits. The Python code should be written in a restricted subset of Python.

    def __init__(self):
        Circuit.__init__(self)
        self.stack: list[dict[str, All]] = [
            {
                "zip": xxzip,
                "concat": xxcon,
                "repeat": xxrep,
                "len": xxlen,
                "slice": xxslc,
                "reverse": xxrev,
                "range": lambda *args: range(*map(asint, args)),
                "fmt": lambda s, *args: asstr(s).format(*map(asint, args)),
                "log": lambda s: print(asstr(s)),
                "gal": lambda x: self.GALOIS(x) if isbin(x) else asgal(x),
                "b8": lambda x: (x + [0x00] * 8)[:8] if isbin(x) else self.BINARY(asgal(x), 8),
                "b16": lambda x: (x + [0x00] * 16)[:16] if isbin(x) else self.BINARY(asgal(x), 16),
                "b32": lambda x: (x + [0x00] * 32)[:32] if isbin(x) else self.BINARY(asgal(x), 32),
                "b64": lambda x: (x + [0x00] * 64)[:64] if isbin(x) else self.BINARY(asgal(x), 64),
                "bin": lambda x, n: (x + [0x00] * asint(n, nat=True))[: asint(n, nat=True)] if isbin(x) else self.BINARY(asgal(x), asint(n, nat=True)),
                "binadd": lambda x, y, c=0x00: self.BINADD(asbin(x), asbin(y), asgal(c)),
                "binsub": lambda x, y, c=0x00: self.BINSUB(asbin(x), asbin(y), asgal(c)),
                "binmul": lambda x, y, c=[], d=[]: self.BINMUL(asbin(x), asbin(y), asbin(c), asbin(d)),
                "divmod": lambda x, y: self.BINDIVMOD(asbin(x), asbin(y)),
                "assert_is_perm": lambda l, r, msg: self.ASSERT_IS_PERM(aslof(l), aslof(r), msg=asstr(msg)),
                "assert_is_bool": lambda x, msg: self.ASSERT_IS_BOOL(asgal(x), msg=asstr(msg)),
                "assert_eqz": lambda x, msg: self.ASSERT_EQZ(asgal(x), msg=asstr(msg)),
                "assert_nez": lambda x, msg: self.ASSERT_NEZ(asgal(x), msg=asstr(msg)),
                "assert_raw": lambda x, y, z, msg: self.MKGATE(asgal(x), asgal(y), asgal(z), msg=asstr(msg)),
                "assert_binle": lambda x, y, msg: self.ASSERT_BINLE(asbin(x), asbin(y), msg=asstr(msg)),
                "assert_binlt": lambda x, y, msg: self.ASSERT_BINLT(asbin(x), asbin(y), msg=asstr(msg)),
                "assert_binge": lambda x, y, msg: self.ASSERT_BINGE(asbin(x), asbin(y), msg=asstr(msg)),
                "assert_bingt": lambda x, y, msg: self.ASSERT_BINGT(asbin(x), asbin(y), msg=asstr(msg)),
            }
        ]  # the stack is used to store the local variables

    def visit(self, node: ast.AST):
        method = "visit_" + node.__class__.__name__
        visitor = getattr(self, method, self.generic_visit)
        try:
            return visitor(node)
        except Exception as e:
            if hasattr(node, "lineno") and hasattr(node, "col_offset"):
                e.add_note("while visiting {} (line {}, column {})".format(node.__class__.__name__, node.lineno, node.col_offset))
            else:
                e.add_note("while visiting {}".format(node.__class__.__name__))
            e.with_traceback(None)
            raise

    def visit_expr(self, node: ast.expr) -> All:
        return self.visit(node)

    def visit_stmt(self, node: ast.stmt) -> Tag:
        return self.visit(node)

    def generic_visit(self, node: ast.AST):
        raise SyntaxError("unsupported syntax")

    def visit_Constant(self, node: ast.Constant) -> All:
        if isinstance(node.value, int):
            return node.value % ρ
        if isinstance(node.value, str):
            return node.value
        raise SyntaxError("invalid constant")

    def visit_Expr(self, node: ast.Expr) -> Tag:
        self.visit_expr(node.value)
        return None, None

    def visit_Pass(self, node: ast.Pass) -> Tag:
        return None, None

    def visit_Continue(self, node: ast.Continue) -> Tag:
        return "continue", None

    def visit_Break(self, node: ast.Break) -> Tag:
        return "break", None

    def visit_Return(self, node: ast.Return) -> Tag:
        return "return", self.visit_expr(node.value) if node.value else None

    def visit_FunctionDef(self, node: ast.FunctionDef) -> Tag:
        func_stack = self.stack

        def func(*args: All) -> All:
            if len(args) != len(node.args.args):
                raise TypeError("mismatched number of arguments")
            call_stack = self.stack
            try:
                self.stack = func_stack + [{target.arg: arg for target, arg in zip(node.args.args, args)}]
                for stmt in node.body:
                    flag, result = self.visit_stmt(stmt)
                    if flag == "break" or flag == "continue":
                        raise SyntaxError("unexpected {}".format(flag))
                    if flag == "return":
                        break
                else:
                    result = None
            finally:
                self.stack = call_stack
            return result

        self.stack[-1][node.name] = func
        return None, None

    def visit_Lambda(self, node: ast.Lambda) -> All:
        func_stack = self.stack

        def func(*args: All) -> All:
            if len(args) != len(node.args.args):
                raise TypeError("mismatched number of arguments")
            call_stack = self.stack
            try:
                self.stack = func_stack + [{target.arg: arg for target, arg in zip(node.args.args, args)}]
                result = self.visit_expr(node.body)
            finally:
                self.stack = call_stack
            return result

        return func

    def visit_Call(self, node: ast.Call) -> All:
        func = self.visit_expr(node.func)
        args = [self.visit_expr(arg) for arg in node.args]
        return func(*args)

    def assign(self, target: ast.expr, value: All):
        if isinstance(target, ast.Tuple):
            if not isinstance(value, tuple) or len(target.elts) != len(value):
                raise TypeError("mismatched number of targets and values in assignment")
            for target, value in zip(target.elts, value):
                self.assign(target, value)
            return
        if isinstance(target, ast.Name):
            self.stack[-1][target.id] = value
            return
        slices = []
        while not isinstance(target, ast.Name):
            if not isinstance(target, ast.Subscript):
                raise SyntaxError("invalid assignment target")
            slices.append(self.visit_expr(target.slice))
            target = target.value
        dest = self.visit_expr(target)
        inner = recursive_shape(dest)
        enums = []
        for slice in reversed(slices):
            keys, inner = inner
            if not isinstance(keys, range | frozenset):
                raise TypeError("invalid item assignment target")
            enums.append(self.ENUM(self.GALOIS(slice) if isbin(slice) else asgal(slice), keys))
        if tuple(inner) != recursive_shape(value):
            raise TypeError("inconsistent shape of target and value in item assignment")
        self.stack[-1][target.id] = self.SETBYKEY(value, dest, *enums)

    def visit_Assign(self, node: ast.Assign) -> Tag:
        value = self.visit_expr(node.value)
        for target in node.targets:
            self.assign(target, value)
        return None, None

    def visit_Delete(self, node: ast.Delete) -> Tag:
        for target in node.targets:
            if not isinstance(target, ast.Name):
                raise SyntaxError("invalid deletion target")
            self.stack[-1].pop(target.id)
        return None, None

    def visit_Name(self, node: ast.Name) -> All:
        for scope in reversed(self.stack):
            if node.id in scope:
                return scope[node.id]
        raise NameError("undefined name: {}".format(node.id))

    def visit_If(self, node: ast.If) -> Tag:
        if asint(self.visit_expr(node.test)):
            for stmt in node.body:
                flag, result = self.visit_stmt(stmt)
                if flag == "continue" or flag == "break" or flag == "return":
                    return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit_stmt(stmt)
                if flag == "continue" or flag == "break" or flag == "return":
                    return flag, result
        return None, None

    def visit_While(self, node: ast.While) -> Tag:
        while asint(self.visit_expr(node.test)):
            for stmt in node.body:
                flag, result = self.visit_stmt(stmt)
                if flag == "continue" or flag == "break" or flag == "return":
                    break
            else:
                continue
            if flag == "continue":
                continue
            if flag == "break":
                break
            if flag == "return":
                return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit_stmt(stmt)
                if flag == "continue" or flag == "break" or flag == "return":
                    return flag, result
        return None, None

    def iterate_over(self, node: ast.comprehension):
        iter = self.visit_expr(node.iter)
        if isinstance(iter, range | frozenset):
            items = iter
        elif isinstance(iter, dict):
            items = iter.items()
        elif isinstance(iter, list):
            items = enumerate(iter)
        else:
            raise TypeError("unsupported iteration object")
        for item in items:
            self.assign(node.target, item)
            yield

    def visit_For(self, node: ast.For) -> Tag:
        for _ in self.iterate_over(node):
            for stmt in node.body:
                flag, result = self.visit_stmt(stmt)
                if flag == "continue" or flag == "break" or flag == "return":
                    break
            else:
                continue
            if flag == "continue":
                continue
            if flag == "break":
                break
            if flag == "return":
                return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit_stmt(stmt)
                if flag == "continue" or flag == "break" or flag == "return":
                    return flag, result
        return None, None

    def visit_ListComp(self, node: ast.ListComp) -> All:
        def visit(generators: list[ast.comprehension]) -> Iterable[All]:
            if len(generators) == 0:
                yield self.visit_expr(node.elt)
                return
            generator, *generators = generators
            call_stack = self.stack
            try:
                self.stack = self.stack + [{}]
                for _ in self.iterate_over(generator):
                    if all(asint(self.visit_expr(test)) for test in generator.ifs):
                        yield from visit(generators)
            finally:
                self.stack = call_stack

        res = list(visit(node.generators))
        if len({recursive_shape(x) for x in res}) > 1:
            raise TypeError("inconsistent shape of list elements")
        return res

    def visit_DictComp(self, node: ast.DictComp) -> All:
        def visit(generators: list[ast.comprehension]) -> Iterable[tuple[Fld, All]]:
            if len(generators) == 0:
                yield asint(self.visit_expr(node.key), sgn=False), self.visit_expr(node.value)
                return
            generator, *generators = generators
            call_stack = self.stack
            try:
                self.stack = self.stack + [{}]
                for _ in self.iterate_over(generator):
                    if all(asint(self.visit_expr(test)) for test in generator.ifs):
                        yield from visit(generators)
            finally:
                self.stack = call_stack

        res = dict(visit(node.generators))
        if len({recursive_shape(x) for x in res.values()}) > 1:
            raise TypeError("inconsistent shape of dict values")
        return res

    def visit_List(self, node: ast.List) -> All:
        res = list(self.visit_expr(elt) for elt in node.elts)
        if len({recursive_shape(x) for x in res}) > 1:
            raise TypeError("inconsistent shape of list elements")
        return res

    def visit_Dict(self, node: ast.Dict) -> All:
        res = dict((asint(self.visit_expr(key), sgn=False), self.visit_expr(value)) for key, value in zip(node.keys, node.values))
        if len({recursive_shape(x) for x in res.values()}) > 1:
            raise TypeError("inconsistent shape of dict values")
        return res

    def visit_Tuple(self, node: ast.Tuple) -> All:
        return tuple(self.visit_expr(elt) for elt in node.elts)

    def visit_Subscript(self, node: ast.Subscript) -> All:
        slice = self.visit_expr(node.slice)
        value = self.visit_expr(node.value)
        keys, inner = recursive_shape(value)
        if isinstance(keys, range):
            return self.GETBYBIN(value, slice if isbin(slice) else self.BINARY(asgal(slice), (len(value) - 1).bit_length()))
        if isinstance(keys, frozenset):
            return self.GETBYKEY(value, self.ENUM(self.GALOIS(slice) if isbin(slice) else asgal(slice), keys))
        raise TypeError("unsupported slicing")

    def visit_Set(self, node: ast.Set) -> All:
        # this syntax is used for summing binary values
        # use * to represent negation (except for the first element)
        # e.g. {a, *b, c, *d, e} represents a - b + c - d + e
        elt, *elts = node.elts
        negs = 0x00
        args = [asbin(self.visit_expr(elt))]
        for elt in elts:
            if isinstance(elt, ast.Starred):
                negs += 0x01
                args.append(self.BITNOT(asbin(self.visit_expr(elt.value))))
            else:
                args.append(asbin(self.visit_expr(elt)))
        return self.BINSUM(args, cGal=negs)

    def visit_BinOp(self, node: ast.BinOp) -> All:
        left = self.visit_expr(node.left)
        right = self.visit_expr(node.right)
        if isinstance(node.op, ast.Add):
            return self.BINADD(left, right)[0] if isbin(left) and isbin(right) else self.ADD(asgal(left), asgal(right))
        if isinstance(node.op, ast.Sub):
            return self.BINSUB(left, right)[0] if isbin(left) and isbin(right) else self.SUB(asgal(left), asgal(right))
        if isinstance(node.op, ast.Mult):
            return self.BINMUL(left, right)[0] if isbin(left) and isbin(right) else self.MUL(asgal(left), asgal(right))
        if isinstance(node.op, ast.Div):
            return self.DIV(asgal(left), asgal(right))
        if isinstance(node.op, ast.Pow):
            return self.BINPOW(left, asbin(right)) if isbin(left) else self.POW(asgal(left), asbin(right))
        if isinstance(node.op, ast.FloorDiv):
            return self.BINDIVMOD(left, right)[0] if isbin(left) and isbin(right) else (asint(left) // asint(right)) % ρ
        if isinstance(node.op, ast.Mod):
            return self.BINDIVMOD(left, right)[1] if isbin(left) and isbin(right) else (asint(left) % asint(right)) % ρ
        if isinstance(node.op, ast.BitAnd):
            return self.BITAND(asbin(left), asbin(right))
        if isinstance(node.op, ast.BitOr):
            return self.BITOR(asbin(left), asbin(right))
        if isinstance(node.op, ast.BitXor):
            return self.BITXOR(asbin(left), asbin(right))
        if isinstance(node.op, ast.LShift):
            return self.SHL(asbin(left), asint(right))
        if isinstance(node.op, ast.RShift):
            return self.SHR(asbin(left), asint(right))
        raise SyntaxError("unsupported binary operation")

    def visit_UnaryOp(self, node: ast.UnaryOp) -> All:
        operand = self.visit_expr(node.operand)
        if isinstance(node.op, ast.Invert):
            return self.BITNOT(asbin(operand))
        if isinstance(node.op, ast.Not):
            return self.NOT(asgal(operand))
        if isinstance(node.op, ast.UAdd):
            return self.ADD(0x00, asgal(operand))
        if isinstance(node.op, ast.USub):
            return self.SUB(0x00, asgal(operand))
        raise SyntaxError("unsupported unary operation")

    def visit_BoolOp(self, node: ast.BoolOp) -> All:
        if isinstance(node.op, ast.And):
            result = 0x01
            for value in node.values:
                result = self.AND(result, asgal(self.visit_expr(value)))
            return result
        if isinstance(node.op, ast.Or):
            result = 0x00
            for value in node.values:
                result = self.OR(result, asgal(self.visit_expr(value)))
            return result
        raise SyntaxError("unsupported boolean operation")

    def visit_Compare(self, node: ast.Compare) -> All:
        result = 0x01
        left = self.visit_expr(node.left)
        for op, right in zip(node.ops, map(self.visit_expr, node.comparators)):
            if isinstance(op, ast.Eq):
                result = self.AND(result, self.NOT(self.NEZ(self.SUB(self.GALOIS(left) if isbin(left) else asgal(left), self.GALOIS(right) if isbin(right) else asgal(right)))))
            elif isinstance(op, ast.NotEq):
                result = self.AND(result, self.NEZ(self.SUB(self.GALOIS(left) if isbin(left) else asgal(left), self.GALOIS(right) if isbin(right) else asgal(right))))
            elif isinstance(op, ast.Lt):
                result = self.AND(result, self.BINLT(left, right) if isbin(left) and isbin(right) else asint(left) < asint(right))
            elif isinstance(op, ast.LtE):
                result = self.AND(result, self.BINLE(left, right) if isbin(left) and isbin(right) else asint(left) <= asint(right))
            elif isinstance(op, ast.Gt):
                result = self.AND(result, self.BINGT(left, right) if isbin(left) and isbin(right) else asint(left) > asint(right))
            elif isinstance(op, ast.GtE):
                result = self.AND(result, self.BINGE(left, right) if isbin(left) and isbin(right) else asint(left) >= asint(right))
            else:
                raise SyntaxError("unsupported comparison")
            left = right
        return result

    def visit_IfExp(self, node: ast.IfExp) -> All:
        left = self.visit_expr(node.body)
        right = self.visit_expr(node.orelse)
        if recursive_shape(left) != recursive_shape(right):
            raise TypeError("inconsistent shape of left and right values in conditional expression")
        return self.IF(asgal(self.visit_expr(node.test)), left, right)


class Compiler(Program):
    def __init__(self):
        Program.__init__(self)
        self.stack[-1].update(
            {
                "secret": lambda s: self.PARAM(asstr(s)),
                "public": lambda s: self.PARAM(asstr(s), public=True),
                "reveal": lambda s, x: self.REVEAL(asstr(s), self.GALOIS(x) if isbin(x) else asgal(x)),
            }
        )

    def compile(self, code: str):
        self.visit(ast.parse(code))

    def visit_Module(self, node: ast.Module):
        for stmt in node.body:
            flag, result = self.visit_stmt(stmt)
            if flag == "continue" or flag == "break" or flag == "return":
                raise SyntaxError("unexpected {}".format(flag))

    def visit_With(self, node: ast.With) -> Tag:
        if len(node.items) != 1:
            raise SyntaxError("invalid with statement")
        item = node.items[0]
        expr = item.context_expr
        vars = item.optional_vars
        if isinstance(expr, ast.Tuple):
            elts = expr.elts
        else:
            elts = [expr]
        inputs = {}
        for elt in elts:
            if not isinstance(elt, ast.Name):
                raise SyntaxError("invalid input target")
            inputs[elt.id] = self.visit_expr(elt)
        if vars is None:
            elts = []
        elif isinstance(vars, ast.Tuple):
            elts = vars.elts
        else:
            elts = [vars]
        outputs = []
        lengths = 0
        for elt in elts:
            slices = []
            length = 1
            while not isinstance(elt, ast.Name):
                if not isinstance(elt, ast.Subscript):
                    raise SyntaxError("invalid output target")
                slice = self.visit_expr(elt.slice)
                slices.append(asint(slice, nat=True))
                length *= slice
                elt = elt.value
            outputs.append((slices, length, elt.id))
            lengths += length

        def func(getw: Getw, args: Args) -> list[Fld]:
            def eval(value: All) -> All:
                if isinstance(value, Fld):
                    return value
                if isinstance(value, Var):
                    return getw(value)
                if isinstance(value, tuple):
                    return tuple(eval(v) for v in value)
                if isinstance(value, list):
                    return list(eval(v) for v in value)
                if isinstance(value, dict):
                    return dict((k, eval(v)) for k, v in value.items())
                raise TypeError("unsupported data type")

            program = Program()
            program.stack[-1]["param"] = lambda s: args[asstr(s)]
            program.stack[-1].update({id: eval(value) for id, value in inputs.items()})
            for stmt in node.body:
                flag, result = program.visit_stmt(stmt)
                if flag == "break" or flag == "continue":
                    raise SyntaxError("unexpected {}".format(flag))
                if flag == "return":
                    break
            else:
                result = None
            if result is None:
                result = []
            elif isinstance(result, tuple):
                result = list(result)
            else:
                result = [result]
            flats = []
            for (slices, length, id), item in zip(outputs, result, strict=True):
                flat = [item]
                for slice in slices:
                    flat = [item for line in flat for item in line]
                flats.extend(flat)
            return flats

        flats = self.MKWIRES(func, lengths)
        for slices, length, id in outputs:
            flat, flats = flats[:length], flats[length:]
            for slice in slices:
                flat = [flat[i : i + slice] for i in range(0, len(flat), slice)]
            self.stack[-1][id] = flat[0]
        return None, None
