import ast
import circuit
import pymcl
ρ = pymcl.r
# check the type of a value
def isgal(x):
    return isinstance(x, (int, circuit.Var))
def isbin(x):
    return isinstance(x, list) and all(isinstance(b, (int, circuit.Var)) for b in x)
# assert the type of a value
def asint(x):
    if isinstance(x, int):
        return (x + (ρ - 1) // 2) % ρ - (ρ - 1) // 2
    raise TypeError('expected a constant value')
def asgal(x):
    if isinstance(x, (int, circuit.Var)):
        return x
    raise TypeError('expected a value')
def asbin(x):
    if isinstance(x, list) and all(isinstance(b, (int, circuit.Var)) for b in x):
        return x
    raise TypeError('expected a binary')
def asstr(x):
    if isinstance(x, str):
        return x
    raise TypeError('expected a string')
# get the shape of a value (binary list will be treated as a list of integers)
def shape(x):
    if isinstance(x, (int, circuit.Var)):
        return (), None
    if isinstance(x, tuple):
        return (), tuple(shape(v) for v in x)
    if isinstance(x, list):
        shapes = {shape(v) for v in x}
        if len(shapes) == 1:
            outer, inner = shapes.pop()
            return (range(len(x)), *outer), inner
        raise TypeError('inconsistent shape of list elements')
    if isinstance(x, dict):
        shapes = {shape(v) for v in x.values()}
        if len(shapes) == 1:
            outer, inner = shapes.pop()
            return (frozenset(x), *outer), inner
        raise TypeError('inconsistent shape of dict values')
    raise TypeError('unsupported data type')
class Compiler(ast.NodeVisitor, circuit.Circuit):
    # The Compiler class is a wrapper of the Circuit class, it compiles the given Python code to the
    # arithmetic circuits. The Python code should be written in a restricted subset of Python.
    def __init__(self):
        ast.NodeVisitor.__init__(self)
        circuit.Circuit.__init__(self)
        self.stack = [{
            'range': lambda *args: range(*map(asint, args)),
            'gal': lambda x: self.GALOIS(x) if isbin(x) else asgal(x),
            'b8':  lambda x: (x + [0x00] *  8)[: 8] if isbin(x) else self.BINARY(asgal(x),  8),
            'b16': lambda x: (x + [0x00] * 16)[:16] if isbin(x) else self.BINARY(asgal(x), 16),
            'b32': lambda x: (x + [0x00] * 32)[:32] if isbin(x) else self.BINARY(asgal(x), 32),
            'b64': lambda x: (x + [0x00] * 64)[:64] if isbin(x) else self.BINARY(asgal(x), 64),
            'bin': lambda x, n: (x + [0x00] * asint(n))[:n] if isbin(x) else self.BINARY(asgal(x), asint(n)),
            'fmt': lambda s, *args: asstr(s).format(*map(asint, args)),
            'log': lambda s: print(asstr(s)),
            'private': lambda s: self.PARAM(asstr(s)),
            'public': lambda s: self.PARAM(asstr(s), public = True),
            'reveal': lambda s, x: self.REVEAL(asstr(s), self.GALOIS(x) if isbin(x) else asgal(x)),
            'isperm': lambda s, d, msg: self.ASSERT_ISPERM(list(map(asgal, s)), list(map(asgal, d)), msg = asstr(msg)),
            'mkgate': lambda x, y, z, msg: self.MKGATE(asgal(x), asgal(y), asgal(z), msg = asstr(msg)),
        }] # the stack is used to store the local variables
    def parse(self, code):
        self.visit(ast.parse(code))
    def visit_Module(self, node):
        for stmt in node.body:
            flag, result = self.visit(stmt)
            if flag == 'continue' or flag == 'break' or flag == 'return':
                raise SyntaxError('unexpected ' + flag)
    def visit_Continue(self, node):
        return 'continue', None
    def visit_Break(self, node):
        return 'break', None
    def visit_Return(self, node):
        return 'return', self.visit(node.value) if node.value else None
    def visit_If(self, node):
        if asint(self.visit(node.test)):
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        return None, None
    def visit_While(self, node):
        while asint(self.visit(node.test)):
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    break
            else:
                continue
            if flag == 'continue':
                continue
            if flag == 'break':
                break
            if flag == 'return':
                return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        return None, None
    def visit_For(self, node):
        if not isinstance(node.target, ast.Name):
            raise SyntaxError('invalid iteration target')
        iter = self.visit(node.iter)
        if isinstance(iter, range):
            iter = iter
        elif isinstance(iter, list):
            iter = range(len(iter))
        elif isinstance(iter, dict):
            iter = iter.keys()
        else:
            raise TypeError('iteration can only be performed on range, list or dict')
        for value in iter:
            self.stack[-1][node.target.id] = value
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    break
            else:
                continue
            if flag == 'continue':
                continue
            if flag == 'break':
                break
            if flag == 'return':
                return flag, result
        else:
            for stmt in node.orelse:
                flag, result = self.visit(stmt)
                if flag == 'continue' or flag == 'break' or flag == 'return':
                    return flag, result
        return None, None
    def visit_ListComp(self, node):
        def visit(generators):
            if len(generators) == 0:
                yield self.visit(node.elt)
                return
            generator, *generators = generators
            if not isinstance(generator.target, ast.Name):
                raise SyntaxError('invalid iteration target')
            iter = self.visit(generator.iter)
            if isinstance(iter, range):
                iter = iter
            elif isinstance(iter, list):
                iter = range(len(iter))
            elif isinstance(iter, dict):
                iter = iter.keys()
            else:
                raise TypeError('iteration can only be performed on range, list or dict')
            call_stack = self.stack
            self.stack = self.stack + [{}]
            for value in iter:
                self.stack[-1][generator.target.id] = value
                if all(asint(self.visit(test)) for test in generator.ifs):
                    yield from visit(generators)
            self.stack = call_stack
        return list(visit(node.generators))
    def visit_DictComp(self, node):
        def visit(generators):
            if len(generators) == 0:
                yield asint(self.visit(node.key)), self.visit(node.value)
                return
            generator, *generators = generators
            if not isinstance(generator.target, ast.Name):
                raise SyntaxError('invalid iteration target')
            iter = self.visit(generator.iter)
            if isinstance(iter, range):
                iter = iter
            elif isinstance(iter, list):
                iter = range(len(iter))
            elif isinstance(iter, dict):
                iter = iter.keys()
            else:
                raise TypeError('iteration can only be performed on range, list or dict')
            call_stack = self.stack
            self.stack = self.stack + [{}]
            for value in iter:
                self.stack[-1][generator.target.id] = value
                if all(asint(self.visit(test)) for test in generator.ifs):
                    yield from visit(generators)
            self.stack = call_stack
        return dict(visit(node.generators))
    def visit_Tuple(self, node):
        return tuple(self.visit(elt) for elt in node.elts)
    def visit_List(self, node):
        return list(self.visit(elt) for elt in node.elts)
    def visit_Dict(self, node):
        return dict((asint(self.visit(key)), self.visit(value)) for key, value in zip(node.keys, node.values))
    def visit_Pass(self, node):
        return None, None
    def visit_Expr(self, node):
        self.visit(node.value)
        return None, None
    def visit_Assert(self, node):
        test = self.visit(node.test)
        if node.msg is None:
            self.ASSERT_NE(0x00, asgal(test))
        else:
            self.ASSERT_NE(0x00, asgal(test), msg = asstr(self.visit(node.msg)))
        return None, None
    def visit_FunctionDef(self, node):
        def_stack = self.stack
        def func(*args):
            if len(args) != len(node.args.args):
                raise TypeError('mismatched number of arguments')
            call_stack = self.stack
            self.stack = def_stack + [{}]
            for target, arg in zip(node.args.args, args):
                self.stack[-1][target.arg] = arg
            for stmt in node.body:
                flag, result = self.visit(stmt)
                if flag == 'break' or flag == 'continue':
                    raise SyntaxError('unexpected ' + flag)
                if flag == 'return':
                    break
            else:
                result = None
            self.stack = call_stack
            return result
        self.stack[-1][node.name] = func
        return None, None
    def visit_Lambda(self, node):
        def_stack = self.stack
        def func(*args):
            if len(args) != len(node.args.args):
                raise TypeError('mismatched number of arguments')
            call_stack = self.stack
            self.stack = def_stack + [{}]
            for target, arg in zip(node.args.args, args):
                self.stack[-1][target.arg] = arg
            result = self.visit(node.body)
            self.stack = call_stack
            return result
        return func
    def visit_Assign(self, node):
        def assign(target, value):
            if isinstance(target, ast.Tuple):
                if not isinstance(value, tuple) or len(target.elts) != len(value):
                    raise TypeError('mismatched number of targets and values in assignment')
                for target, value in zip(target.elts, value):
                    assign(target, value)
                return
            if isinstance(target, ast.Name):
                self.stack[-1][target.id] = value
                return
            slices = []
            while not isinstance(target, ast.Name):
                if not isinstance(target, ast.Subscript):
                    raise SyntaxError('invalid assignment target')
                slices.append(self.visit(target.slice))
                target = target.value
            dest = self.visit(target)
            outer, inner = shape(dest)
            enums = []
            for slice in reversed(slices):
                if len(outer) == 0:
                    raise TypeError('cannot index a scalar')
                keys, *outer = outer
                enums.append(self.ENUM(self.GALOIS(slice) if isbin(slice) else asgal(slice), keys))
            if (tuple(outer), inner) != shape(value):
                raise TypeError('inconsistent shape of target and value in indexed assignment')
            self.stack[-1][target.id] = self.SETBYKEY(value, dest, *enums)
        value = self.visit(node.value)
        for target in node.targets:
            assign(target, value)
        return None, None
    def visit_Delete(self, node):
        for target in node.targets:
            if not isinstance(target, ast.Name):
                raise SyntaxError('invalid deletion target')
            self.stack[-1].pop(target.id)
        return None, None
    def visit_Name(self, node):
        for scope in reversed(self.stack):
            if node.id in scope:
                return scope[node.id]
        raise NameError('undefined name: {}'.format(node.id))
    def visit_Subscript(self, node):
        slice = self.visit(node.slice)
        value = self.visit(node.value)
        outer, inner = shape(value)
        if len(outer) == 0:
            raise TypeError('cannot index a scalar')
        if isinstance(value, list): # optimize for list
            return self.GETBYBIN(value, slice if isbin(slice) else self.BINARY(asgal(slice), (len(value) - 1).bit_length()))
        keys, *outer = outer
        return self.GETBYKEY(value, self.ENUM(self.GALOIS(slice) if isbin(slice) else asgal(slice), keys))
    def visit_Call(self, node):
        return self.visit(node.func)(*map(self.visit, node.args))
    def visit_Set(self, node):
        # this syntax is used for summing binary values
        # use * to represent negation (except for the first element)
        # e.g. {a, *b, c, *d, e} represents a - b + c - d + e
        elt, *elts = node.elts
        negs = 0x00
        args = [asbin(self.visit(elt))]
        for elt in elts:
            if isinstance(elt, ast.Starred):
                negs += 0x01
                args.append(self.BITNOT(asbin(self.visit(elt.value))))
            else:
                args.append(asbin(self.visit(elt)))
        return self.BINSUM(args, cGal = negs)
    def visit_Constant(self, node):
        if isinstance(node.value, int):
            return node.value % ρ
        if isinstance(node.value, str):
            return node.value
        raise SyntaxError('invalid constant')
    def visit_BinOp(self, node):
        left = self.visit(node.left)
        right = self.visit(node.right)
        if isinstance(node.op, ast.Add):
            return self.BINADD(left, right)[0] if isbin(left) and isbin(right) else self.ADD(asgal(left), asgal(right))
        if isinstance(node.op, ast.Sub):
            return self.BINSUB(left, right)[0] if isbin(left) and isbin(right) else self.SUB(asgal(left), asgal(right))
        if isinstance(node.op, ast.Mult):
            return self.BINMUL(left, right)[0] if isbin(left) and isbin(right) else self.MUL(asgal(left), asgal(right))
        if isinstance(node.op, ast.Div):
            return self.DIV(asgal(left), asgal(right))
        if isinstance(node.op, ast.Pow):
            return self.POW(left, asbin(right)) if isbin(left) else self.BINPOW(asgal(left), asbin(right))
        if isinstance(node.op, ast.FloorDiv):
            return self.BINDIVMOD(asbin(left), asbin(right))[0]
        if isinstance(node.op, ast.Mod):
            return self.BINDIVMOD(asbin(left), asbin(right))[1]
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
        raise SyntaxError('unsupported binary operation')
    def visit_UnaryOp(self, node):
        operand = self.visit(node.operand)
        if isinstance(node.op, ast.Invert):
            return self.BITNOT(asbin(operand))
        if isinstance(node.op, ast.Not):
            return self.NOT(asgal(operand))
        if isinstance(node.op, ast.UAdd):
            return self.ADD(0x00, asgal(operand))
        if isinstance(node.op, ast.USub):
            return self.SUB(0x00, asgal(operand))
        raise SyntaxError('unsupported unary operation')
    def visit_BoolOp(self, node):
        if isinstance(node.op, ast.And):
            result = 0x01
            for value in node.values:
                result = self.AND(result, asgal(self.visit(value)))
            return result
        if isinstance(node.op, ast.Or):
            result = 0x00
            for value in node.values:
                result = self.OR(result, asgal(self.visit(value)))
            return result
        raise SyntaxError('unsupported boolean operation')
    def visit_Compare(self, node):
        result = 0x01
        left = self.visit(node.left)
        for op, right in zip(node.ops, map(self.visit, node.comparators)):
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
                raise SyntaxError('unsupported comparison')
            left = right
        return result
    def visit_IfExp(self, node):
        left = self.visit(node.body)
        right = self.visit(node.orelse)
        if shape(left) != shape(right):
            raise TypeError('inconsistent shape of left and right values in conditional expression')
        return self.IF(asgal(self.visit(node.test)), left, right)
    def generic_visit(self, node):
        raise SyntaxError('unsupported syntax')
    def visit_Index(self, node):
        # deprecated since Python 3.9
        return self.visit(node.value)