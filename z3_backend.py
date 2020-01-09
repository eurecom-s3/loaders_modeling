import logging
import coloredlogs
log = logging.getLogger(__name__)
log.setLevel(logging.DEBUG)
coloredlogs.install(level="DEBUG", logger=log)

import z3

from classes import Base, Immediate, Variable, Expression

def SUB(a, b):
    return a - b

def EQ(a, b):
    return a == b

def NEQ(a, b):
    return a != b

def BITOR(a, b):
    return a | b

def BITAND(a, b):
    return a & b

def GE(a, b):
    return a >= b

def Slice(var, start, cnt=1):
    if isinstance(start, z3.BitVecRef):
        zeroext = z3.ZeroExt(var.size() - start.size(), start)
        shifted = z3.LShR(var, zeroext*8)
        var = shifted
    else:
        shifted = z3.LShR(var, start)
        var = shifted

    if isinstance(cnt, z3.BitVecRef):
        cnt = cnt.as_long()
    return z3.Extract((cnt * 8) - 1, 0, var)

z3_funcs = {'ADD'   : z3.Sum,
            'SUB'   : SUB,
            'UDIV'  : z3.UDiv,
            'AND'   : z3.And,
            'OR'    : z3.Or,
            'NOT'   : z3.Not,
            'ULE'   : z3.ULE,
            'EQ'    : EQ,
            'NEQ'   : NEQ,
            'GE'    : GE,
            'BITOR' : BITOR,
            'BITAND': BITAND,
            'Slice' : Slice,
}

z3_funcs_sized = {'ADD', 'SUB', 'UDIV', 'EQ', 'NEQ', 'GE', 'ULE', 'BITOR', 'BITAND'}
z3_funcs_bool  = {'OR', 'AND', 'NOT'}
z3_funcs_unsigned = {'BITOR', 'BITAND', 'ULE'}

def dispatch_z3_2(func, arg1, arg2):
    if func not in z3_funcs:
        log.critical(f"Function {func} not recognized")
        raise NameError
    if func in z3_funcs_sized:
        max_size = max(arg1.size, arg2.size)
        extension_mechanism = (z3.ZeroExt if func in z3_funcs_unsigned
                               else z3.SignExt)
        if arg1.size != max_size:
            arg1 = Expression(extension_mechanism(max_size - arg1.size,
                                                  arg1.symb))
        if arg2.size != max_size:
            arg2 = Expression(extension_mechanism(max_size - arg2.size,
                                                  arg2.symb))
    arg1 = arg1.symb
    arg2 = arg2.symb
    return z3_funcs[func](arg1, arg2)

def dispatch_z3_3(func, *args):
    if func != "Slice":
        log.CRITICAL(f"{func} not recognized as a 3-arguments function")
        raise ValueError
    args = [arg.symb for arg in args]
    return z3_funcs[func](*args)

def dispatch_z3(func, *args):
    if not 0 < len(args) < 4:
        log.critical(f"Trying to dispatch function with {len(args)}"
                     " arguments")
        raise TypeError
    if len(args) == 1:
        pass
    elif len(args) == 2:
        return dispatch_z3_2(func, *args)
    elif len(args) == 3:
        return dispatch_z3_3(func, *args)
