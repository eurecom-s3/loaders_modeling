#### This code is from angr
#### Check out the original at
#### https://github.com/angr/angr/blob/461b392e32e9535667fa4b35bd87bf46b4f06f31/angr/sim_type.py

from collections import OrderedDict, defaultdict
import copy
import re
import logging


l = logging.getLogger(name=__name__)

# pycparser hack to parse type expressions
errorlog = logging.getLogger(name=__name__)
errorlog.setLevel(logging.INFO)

try:
    import pycparser
except ImportError:
    pycparser = None


class SimType:
    """
    SimType exists to track type information for SimProcedures.
    """

    _fields = ()
    _size = None
    base = True

    def __init__(self, label=None):
        """
        :param label: the type label.
        """
        self.label = label

    def __eq__(self, other):
        if type(self) != type(other):
            return False

        for attr in self._fields:
            if getattr(self, attr) != getattr(other, attr):
                return False

        return True

    def __ne__(self, other):
        # wow many efficient
        return not self == other

    def __hash__(self):
        # very hashing algorithm many secure wow
        out = hash(type(self))
        for attr in self._fields:
            out ^= hash(getattr(self, attr))
        return out

    @property
    def name(self):
        return repr(self)

    @property
    def size(self):
        """
        The size of the type in bits.
        """
        if self._size is not None:
            return self._size
        return NotImplemented


class SimTypeBottom(SimType):
    """
    SimTypeBottom basically represents a type error.
    """

    def __repr__(self):
        return 'BOT'


class SimTypeTop(SimType):
    """
    SimTypeTop represents any type (mostly used with a pointer for void*).
    """

    _fields = ('size',)

    def __init__(self, size=None, label=None):
        SimType.__init__(self, label)
        self._size = size

    def __repr__(self):
        return 'TOP'


class SimTypeReg(SimType):
    """
    SimTypeReg is the base type for all types that are register-sized.
    """

    _fields = ('size',)

    def __init__(self, size, label=None):
        """
        :param label: the type label.
        :param size: the size of the type (e.g. 32bit, 8bit, etc.).
        """
        SimType.__init__(self, label=label)
        self._size = size

    def __repr__(self):
        return "reg{}_t".format(self.size)

class SimTypeNum(SimType):
    """
    SimTypeNum is a numeric type of arbitrary length
    """

    _fields = SimType._fields + ('signed', 'size')

    def __init__(self, size, signed=True, label=None):
        """
        :param size:        The size of the integer, in bytes
        :param signed:      Whether the integer is signed or not
        :param label:       A label for the type
        """
        super(SimTypeNum, self).__init__(label)
        self._size = size
        self.signed = signed

    def __repr__(self):
        return "{}int{}_t".format('' if self.signed else 'u', self.size)

class SimTypeInt(SimTypeReg):
    """
    SimTypeInt is a type that specifies a signed or unsigned C integer.
    """

    _fields = SimTypeReg._fields + ('signed',)
    _base_name = 'int'

    def __init__(self, signed=True, label=None):
        """
        :param signed:  True if signed, False if unsigned
        :param label:   The type label
        """
        super(SimTypeInt, self).__init__(None, label=label)
        self.signed = signed

    def __repr__(self):
        name = self._base_name
        if not self.signed:
            name = 'unsigned ' + name

        try:
            return name + ' (%d bits)' % self.size
        except ValueError:
            return name

    @property
    def size(self):
        try:
            return DEFAULT_SIZES[self._base_name]
        except KeyError:
            raise ValueError(f"Type {self._base.name} unknown")


class SimTypeShort(SimTypeInt):
    _base_name = 'short'


class SimTypeLong(SimTypeInt):
    _base_name = 'long'


class SimTypeLongLong(SimTypeInt):
    _base_name = 'long long'


class SimTypeChar(SimTypeReg):
    """
    SimTypeChar is a type that specifies a character;
    this could be represented by a byte, but this is meant to be interpreted as a character.
    """

    def __init__(self, label=None):
        """
        :param label: the type label.
        """
        # FIXME: Now the size of a char is state-dependent.
        SimTypeReg.__init__(self, 8, label=label)
        self.signed = False

    def __repr__(self):
        return 'char'


class SimTypeBool(SimTypeChar):
    def __repr__(self):
        return 'bool'


class SimTypeFd(SimTypeReg):
    """
    SimTypeFd is a type that specifies a file descriptor.
    """

    _fields = SimTypeReg._fields

    def __init__(self, label=None):
        """
        :param label: the type label
        """
        # file descriptors are always 32 bits, right?
        # TODO: That's so closed-minded!
        super(SimTypeFd, self).__init__(32, label=label)

    def __repr__(self):
        return 'fd_t'


class SimTypePointer(SimTypeReg):
    """
    SimTypePointer is a type that specifies a pointer to some other type.
    """

    _fields = SimTypeReg._fields + ('pts_to',)

    def __init__(self, pts_to, label=None, offset=0):
        """
        :param label:   The type label.
        :param pts_to:  The type to which this pointer points to.
        """
        super(SimTypePointer, self).__init__(None, label=label)
        self.pts_to = pts_to
        self.signed = False
        self.offset = offset

    def __repr__(self):
        return '{}*'.format(self.pts_to)

    @property
    def size(self):
        return DEFAULT_BITS


class SimTypeFixedSizeArray(SimType):
    """
    SimTypeFixedSizeArray is a literal (i.e. not a pointer) fixed-size array.
    """

    def __init__(self, elem_type, length):
        super(SimTypeFixedSizeArray, self).__init__()
        self.elem_type = elem_type
        self.length = length

    def __repr__(self):
        return '{}[{}]'.format(self.elem_type, self.length)

    @property
    def size(self):
        return self.elem_type.size * self.length

    @property
    def alignment(self):
        return self.elem_type.alignment


class SimTypeArray(SimType):
    """
    SimTypeArray is a type that specifies a pointer to an array; while it is a pointer, it has a semantic difference.
    """

    _fields = ('elem_type', 'length')

    def __init__(self, elem_type, length=None, label=None):
        """
        :param label:       The type label.
        :param elem_type:   The type of each element in the array.
        :param length:      An expression of the length of the array, if known.
        """
        super(SimTypeArray, self).__init__(label=label)
        self.elem_type = elem_type
        self.length = length

    def __repr__(self):
        return '{}[{}]'.format(self.elem_type, '' if self.length is None else self.length)

    @property
    def size(self):
        return DEFAULT_BITS

    @property
    def alignment(self):
        return self.elem_type.alignment


class SimTypeString(SimTypeArray):
    """
    SimTypeString is a type that represents a C-style string,
    i.e. a NUL-terminated array of bytes.
    """

    _fields = SimTypeArray._fields + ('length',)

    def __init__(self, length=None, label=None):
        """
        :param label:   The type label.
        :param length:  An expression of the length of the string, if known.
        """
        super(SimTypeString, self).__init__(SimTypeChar(), label=label, length=length)

    def __repr__(self):
        return 'string_t'

    @property
    def size(self):
        if self.length is None:
            return 4096         # :/
        return (self.length + 1) * 8

    @property
    def alignment(self):
        return 1


class SimTypeWString(SimTypeArray):
    """
    A wide-character null-terminated string, where each character is 2 bytes.
    """

    _fields = SimTypeArray._fields + ('length',)

    def __init__(self, length=None, label=None):
        super(SimTypeWString, self).__init__(SimTypeNum(16, False), label=label, length=length)

    def __repr__(self):
        return 'wstring_t'

    @property
    def size(self):
        if self.length is None:
            return 4096
        return (self.length * 2 + 2) * 8

    @property
    def alignment(self):
        return 2


class SimTypeFunction(SimType):
    """
    SimTypeFunction is a type that specifies an actual function (i.e. not a pointer) with certain types of arguments and
    a certain return value.
    """

    _fields = ('args', 'returnty')
    base = False

    def __init__(self, args, returnty, label=None, arg_names=None):
        """
        :param label:    The type label
        :param args:     A tuple of types representing the arguments to the function
        :param returnty: The return type of the function, or none for void
        """
        super(SimTypeFunction, self).__init__(label=label)
        self.args = args
        self.returnty = returnty
        self.arg_names = arg_names if arg_names else []

    def __repr__(self):
        return '({}) -> {}'.format(', '.join(str(a) for a in self.args), self.returnty)

    @property
    def size(self):
        return 4096     # ???????????


class SimTypeLength(SimTypeLong):
    """
    SimTypeLength is a type that specifies the length of some buffer in memory.

    ...I'm not really sure what the original design of this class was going for
    """

    _fields = SimTypeNum._fields + ('addr', 'length') # ?

    def __init__(self, signed=False, addr=None, length=None, label=None):
        """
        :param signed:  Whether the value is signed or not
        :param label:   The type label.
        :param addr:    The memory address (expression).
        :param length:  The length (expression).
        """
        super(SimTypeLength, self).__init__(signed=signed, label=label)
        self.addr = addr
        self.length = length

    def __repr__(self):
        return 'size_t'

    @property
    def size(self):
        return DEFAULT_BITS


class SimTypeFloat(SimTypeReg):
    """
    An IEEE754 single-precision floating point number
    """
    def __init__(self, size=32):
        super(SimTypeFloat, self).__init__(size)

    signed = True

    def __repr__(self):
        return 'float'


class SimTypeDouble(SimTypeFloat):
    """
    An IEEE754 double-precision floating point number
    """
    def __init__(self, align_double=True):
        self.align_double = align_double
        super(SimTypeDouble, self).__init__(64)

    def __repr__(self):
        return 'double'

    @property
    def alignment(self):
        return 8 if self.align_double else 4


class SimStruct(SimType):
    _fields = ('name', 'fields')

    def __init__(self, fields, name=None, pack=False, align=None):
        super(SimStruct, self).__init__(None)
        self._pack = pack
        self._name = '<anon>' if name is None else name
        self._align = align
        self._pack = pack
        self.fields = fields

    @property
    def name(self): # required bc it's a property in the original
        return self._name

    @property
    def offsets(self):
        offsets = {}
        offset_so_far = 0
        for name, ty in self.fields.items():
            offsets[name] = offset_so_far
            offset_so_far += ty.size // 8

        return offsets

    def __repr__(self):
        return 'struct %s' % self.name

    @property
    def size(self):
        return sum(val.size for val in self.fields.values())

    @property
    def alignment(self):
        if self._align is not None:
            return self._align
        return max(val.alignment for val in self.fields.values())


class SimStructValue:
    """
    A SimStruct type paired with some real values
    """
    def __init__(self, struct, values=None):
        """
        :param struct:      A SimStruct instance describing the type of this struct
        :param values:      A mapping from struct fields to values
        """
        self._struct = struct
        self._values = defaultdict(lambda: None, values or ())

    def __repr__(self):
        fields = ('.{} = {}'.format(name, self._values[name]) for name in self._struct.fields)
        return '{{\n  {}\n}}'.format(',\n  '.join(fields))

    def __getattr__(self, k):
        return self[k]

    def __getitem__(self, k):
        if type(k) is int:
            return self._values[self._struct.fields[k]]
        return self._values[k]


class SimUnion(SimType):
    _fields = ('members', 'name')

    def __init__(self, members, name=None, label=None):
        """
        :param members:     The members of the union, as a mapping name -> type
        :param name:        The name of the union
        """
        super(SimUnion, self).__init__(label)
        self._name = name if name is not None else '<anon>'
        self.members = members

    @property
    def name(self):
        return self._name

    @property
    def size(self):
        return max(ty.size for ty in self.members.values())

    @property
    def alignment(self):
        return max(val.alignment for val in self.members.values())

    def __repr__(self):
        # use the str instead of repr of each member to avoid exceed recursion
        # depth when representing self-referential unions
        return 'union %s {\n\t%s\n}' % (self.name, '\n\t'.join('%s %s;' % (name, str(ty)) for name, ty in self.members.items()))

    def __str__(self):
        return 'union %s' % (self.name, )

DEFAULT_SIZES = {
    'char'      : 8,
    'short'     : 16,
    'int'       : 32,
    'long'      : 64,
    'long long' : 64
}
DEFAULT_BITS = 64

BASIC_TYPES = {
    'char': SimTypeNum(DEFAULT_SIZES['char'], True),
    'signed char': SimTypeNum(DEFAULT_SIZES['char'], True),
    'unsigned char': SimTypeNum(DEFAULT_SIZES['char'], False),

    'short': SimTypeNum(DEFAULT_SIZES['short'], True),
    'signed short': SimTypeNum(DEFAULT_SIZES['short'], True),
    'unsigned short': SimTypeNum(DEFAULT_SIZES['short'], False),
    'short int': SimTypeNum(DEFAULT_SIZES['short'], True),
    'signed short int': SimTypeNum(DEFAULT_SIZES['short'], True),
    'unsigned short int': SimTypeNum(DEFAULT_SIZES['short'], False),

    'int': SimTypeNum(DEFAULT_SIZES['int'], True),
    'signed int': SimTypeNum(DEFAULT_SIZES['int'], True),
    'unsigned int': SimTypeNum(DEFAULT_SIZES['int'], False),

    'long': SimTypeNum(DEFAULT_SIZES['long'], True),
    'signed long': SimTypeNum(DEFAULT_SIZES['long'], True),
    'unsigned long': SimTypeNum(DEFAULT_SIZES['long'], False),
    'long int': SimTypeNum(DEFAULT_SIZES['long'], True),
    'signed long int': SimTypeNum(DEFAULT_SIZES['long'], True),
    'unsigned long int': SimTypeNum(DEFAULT_SIZES['long'], False),

    'long long' : SimTypeNum(DEFAULT_SIZES['long long'], True),
    'signed long long': SimTypeNum(DEFAULT_SIZES['long long'], True),
    'unsigned long long': SimTypeNum(DEFAULT_SIZES['long long'], False),
    'long long int': SimTypeNum(DEFAULT_SIZES['long long'], True),
    'signed long long int': SimTypeNum(DEFAULT_SIZES['long long'], True),
    'unsigned long long int': SimTypeNum(DEFAULT_SIZES['long long'], False),

    'float': SimTypeFloat(),
    'double': SimTypeDouble(),
    'void': SimTypeBottom(),
}


ALL_TYPES = {
    'int8_t': SimTypeNum(8, True),
    'uint8_t': SimTypeNum(8, False),
    'byte': SimTypeNum(8, False),

    'int16_t': SimTypeNum(16, True),
    'uint16_t': SimTypeNum(16, False),
    'word': SimTypeNum(16, False),

    'int32_t': SimTypeNum(32, True),
    'uint32_t': SimTypeNum(32, False),
    'dword': SimTypeNum(32, False),

    'int64_t': SimTypeNum(64, True),
    'uint64_t': SimTypeNum(64, False),
    'qword': SimTypeNum(64, False),

    'ptrdiff_t': SimTypeLong(True),
    'size_t': SimTypeLength(False),
    'ssize_t': SimTypeLength(True),
    'ssize': SimTypeLength(False),
    'uintptr_t': SimTypeLong(False),

    'string': SimTypeString(),
    'wstring': SimTypeWString(),
}


ALL_TYPES.update(BASIC_TYPES)

def update_types(new_types):
    ALL_TYPES.update(new_types)


# this is a hack, pending https://github.com/eliben/pycparser/issues/187
def make_preamble():
    out = ['typedef int TOP;']
    types_out = []
    for ty in ALL_TYPES:
        if ty in BASIC_TYPES:
            continue
        if ' ' in ty:
            continue

        typ = ALL_TYPES[ty]
        if isinstance(typ, (SimTypeFunction, SimTypeString, SimTypeWString)):
            continue

        if isinstance(typ, (SimTypeNum, SimTypeInt)) and str(typ) not in BASIC_TYPES:
            try:
                # TODO: Investigate whether this needs to be re-imagined using byte_width
                styp = {8: 'char', 16: 'short', 32: 'int', 64: 'long long'}[typ._size]
            except KeyError:
                styp = 'long' # :(
            if not typ.signed:
                styp = 'unsigned ' + styp
            typ = styp

        if isinstance(typ, (SimStruct,)):
            types_out.append(str(typ))

        out.append('typedef %s %s;' % (typ, ty))
        types_out.append(ty)

    return '\n'.join(out) + '\n', types_out

def _make_scope():
    """
    Generate CParser scope_stack argument to parse method
    """
    scope = dict()
    for ty in ALL_TYPES:
        if ty in BASIC_TYPES:
            continue
        if ' ' in ty:
            continue

        typ = ALL_TYPES[ty]
        if isinstance(typ, (SimTypeFunction,SimTypeString, SimTypeWString)):
            continue

        scope[ty] = True
    return [scope]


def define_struct(defn):
    """
    Register a struct definition globally

    >>> define_struct('struct abcd {int x; int y;}')
    """
    struct = parse_type(defn)
    ALL_TYPES[struct.name] = struct
    ALL_TYPES['struct ' + struct.name] = struct
    return struct


def register_types(types):
    """
    Pass in some types and they will be registered to the global type store.

    The argument may be either a mapping from name to SimType, or a plain SimType.
    The plain SimType must be either a struct or union type with a name present.

    >>> register_types(parse_types("typedef int x; typedef float y;"))
    >>> register_types(parse_type("struct abcd { int ab; float cd; }"))
    """
    if type(types) is SimStruct:
        if types.name == '<anon>':
            raise ValueError("Cannot register anonymous struct")
        ALL_TYPES['struct ' + types.name] = types
    elif type(types) is SimUnion:
        if types.name == '<anon>':
            raise ValueError("Cannot register anonymous union")
        ALL_TYPES['union ' + types.name] = types
    else:
        ALL_TYPES.update(types)


def do_preprocess(defn):
    """
    Run a string through the C preprocessor that ships with pycparser but is weirdly inaccessible?
    """
    from pycparser.ply import lex, cpp
    lexer = lex.lex(cpp)
    p = cpp.Preprocessor(lexer)
    p.parse(defn)
    return ''.join(tok.value for tok in p.parser if tok.type not in p.ignore)


def parse_defns(defn, preprocess=True):
    """
    Parse a series of C definitions, returns a mapping from variable name to variable type object
    """
    return parse_file(defn, preprocess=preprocess)[0]


def parse_types(defn, preprocess=True):
    """
    Parse a series of C definitions, returns a mapping from type name to type object
    """
    return parse_file(defn, preprocess=preprocess)[1]


_include_re = re.compile(r'^\s*#include')
def parse_file(defn, preprocess=True):
    """
    Parse a series of C definitions, returns a tuple of two type mappings, one for variable
    definitions and one for type definitions.
    """
    if pycparser is None:
        raise ImportError("Please install pycparser in order to parse C definitions")

    defn = '\n'.join(x for x in defn.split('\n') if _include_re.match(x) is None)

    if preprocess:
        defn = do_preprocess(defn)

    preamble, ignoreme = make_preamble()
    node = pycparser.c_parser.CParser().parse(preamble + defn)
    if not isinstance(node, pycparser.c_ast.FileAST):
        raise ValueError("Something went horribly wrong using pycparser")
    out = {}
    extra_types = {}
    for piece in node.ext:
        if isinstance(piece, pycparser.c_ast.FuncDef):
            out[piece.decl.name] = _decl_to_type(piece.decl.type, extra_types)
        elif isinstance(piece, pycparser.c_ast.Decl):
            ty = _decl_to_type(piece.type, extra_types)
            if piece.name is not None:
                out[piece.name] = ty
        elif isinstance(piece, pycparser.c_ast.Typedef):
            extra_types[piece.name] = _decl_to_type(piece.type, extra_types)

    for ty in ignoreme:
        del extra_types[ty]
    return out, extra_types


def parse_type(defn, preprocess=True):
    """
    Parse a simple type expression into a SimType

    >>> parse_type('int *')
    """
    if pycparser is None:
        raise ImportError("Please install pycparser in order to parse C definitions")

    defn = re.sub(r"/\*.*?\*/", r"", defn)

    parser = pycparser.CParser()

    parser.cparser = pycparser.ply.yacc.yacc(module=parser,
                                             start='parameter_declaration',
                                             debug=False,
                                             optimize=False,
                                             errorlog=errorlog)

    node = parser.parse(text=defn, scope_stack=_make_scope())
    if not isinstance(node, pycparser.c_ast.Typename) and \
            not isinstance(node, pycparser.c_ast.Decl):
        raise ValueError("Something went horribly wrong using pycparser")

    decl = node.type
    return _decl_to_type(decl)


def _accepts_scope_stack():
    """
    pycparser hack to include scope_stack as parameter in CParser parse method
    """
    def parse(self, text, scope_stack=None, filename='', debuglevel=0):
        self.clex.filename = filename
        self.clex.reset_lineno()
        self._scope_stack = [dict()] if scope_stack is None else scope_stack
        self._last_yielded_token = None
        return self.cparser.parse(
            input=text,
            lexer=self.clex,
            debug=debuglevel)
    setattr(pycparser.CParser, 'parse', parse)


def _decl_to_type(decl, extra_types=None):
    if extra_types is None: extra_types = {}

    if isinstance(decl, pycparser.c_ast.FuncDecl):
        argtyps = () if decl.args is None else [_decl_to_type(x.type, extra_types) for x in decl.args.params]
        arg_names = [ arg.name for arg in decl.args.params] if decl.args else None
        return SimTypeFunction(argtyps, _decl_to_type(decl.type, extra_types), arg_names=arg_names)

    elif isinstance(decl, pycparser.c_ast.TypeDecl):
        if decl.declname == 'TOP':
            return SimTypeTop()
        return _decl_to_type(decl.type, extra_types)

    elif isinstance(decl, pycparser.c_ast.PtrDecl):
        pts_to = _decl_to_type(decl.type, extra_types)
        return SimTypePointer(pts_to)

    elif isinstance(decl, pycparser.c_ast.ArrayDecl):
        elem_type = _decl_to_type(decl.type, extra_types)
        try:
            size = _parse_const(decl.dim)
        except ValueError as e:
            l.warning("Got error parsing array dimension, defaulting to zero: %s", e)
            size = 0
        return SimTypeFixedSizeArray(elem_type, size)

    elif isinstance(decl, pycparser.c_ast.Struct):
        if decl.decls is not None:
            fields = OrderedDict((field.name, _decl_to_type(field.type, extra_types)) for field in decl.decls)
        else:
            fields = OrderedDict()

        if decl.name is not None:
            key = 'struct ' + decl.name
            if key in extra_types:
                struct = extra_types[key]
            elif key in ALL_TYPES:
                struct = ALL_TYPES[key]
            else:
                struct = None

            if struct is None:
                struct = SimStruct(fields, decl.name)
            elif not struct.fields:
                struct.fields = fields
            elif fields and struct.fields != fields:
                raise ValueError("Redefining body of " + key)

            extra_types[key] = struct
        else:
            struct = SimStruct(fields)
        return struct

    elif isinstance(decl, pycparser.c_ast.Union):
        if decl.decls is not None:
            fields = {field.name: _decl_to_type(field.type, extra_types) for field in decl.decls}
        else:
            fields = {}

        if decl.name is not None:
            key = 'union ' + decl.name
            if key in extra_types:
                union = extra_types[key]
            elif key in ALL_TYPES:
                union = ALL_TYPES[key]
            else:
                union = None

            if union is None:
                union = SimUnion(fields, decl.name)
            elif not union.members:
                union.members = fields
            elif fields and union.members != fields:
                raise ValueError("Redefining body of " + key)

            extra_types[key] = union
        else:
            union = SimUnion(fields)
        return union

    elif isinstance(decl, pycparser.c_ast.IdentifierType):
        key = ' '.join(decl.names)
        if key in extra_types:
            return extra_types[key]
        elif key in ALL_TYPES:
            return ALL_TYPES[key]
        else:
            raise TypeError("Unknown type '%s'" % ' '.join(key))

    raise ValueError("Unknown type!")


def _parse_const(c):
    if type(c) is pycparser.c_ast.Constant:
        return int(c.value)
    elif type(c) is pycparser.c_ast.BinaryOp:
        if c.op == '+':
            return _parse_const(c.children()[0][1]) + _parse_const(c.children()[1][1])
        if c.op == '-':
            return _parse_const(c.children()[0][1]) - _parse_const(c.children()[1][1])
        if c.op == '*':
            return _parse_const(c.children()[0][1]) * _parse_const(c.children()[1][1])
        if c.op == '/':
            return _parse_const(c.children()[0][1]) // _parse_const(c.children()[1][1])
        raise ValueError('Binary op %s' % c.op)
    else:
        raise ValueError(c)

if pycparser is not None:
    _accepts_scope_stack()

try:
    register_types(parse_types("""
typedef long time_t;

struct timespec {
    time_t tv_sec;
    long tv_nsec;
};

struct timeval {
    time_t tv_sec;
    long tv_usec;
};
"""))
except ImportError:
    pass
