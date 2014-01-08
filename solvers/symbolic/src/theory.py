# Author: Garvit Juniwal (garvitjuniwal@eecs.berkeley.edu)

# This file contains the meaning of theory symbols
# Currently supported theories are QF_LIA and QF_BV

from z3 import *  # @UnusedWildImport

def _BVAnd(a, b):
    return a & b

def _BVOr(a, b):
    return a | b

def _BVNot(a):
    return ~a

def _BVSub(a, b):
    return a - b

def _BVAdd(a, b):
    return a + b

def _BVXor(a, b):
    return a ^ b

def _BVUgt(a, b):
    return UGT(a, b)

def _BVUge(a, b):
    return UGE(a, b)

def _Equal(a, b):
    return a == b

def _BVMul(a, b):
    return a * b

def _BVUdiv(a, b):
    return UDiv(a, b)

def _BVUrem(a, b):
    return URem(a, b)

def _BVLshr(a, b):
    return LShR(a, b)

def _BVAshr(a, b):
    return a >> b

def _BVShl(a, b):
    return a << b

def _BVSdiv(a, b):
    return a / b

def _BVSrem(a, b):
    return SRem(a, b)

def _BVNeg(a):
    return -a

def _BVUlt(a, b):
    return ULT(a, b)

def _BVUle(a, b):
    return ULE(a, b)

def _BVSle(a, b):
    return a <= b

def _BVSlt(a, b):
    return a < b

def _BVRedor(a):
    if is_bv_sort(a.sort()):
        return Not(a == BitVecVal(0, a.sort().size()))
    else:
        raise Exception('Cannot call bvredor on non-bv')

def _IntAdd(a, b):
    return a + b

def _IntSub(a, b):
    return a - b
    
def _ITE(a, b, c):
    return If(a, b, c)
    
def _BoolAnd(a, b):
    return And(a, b)

def _BoolOr(a, b):
    return Or(a, b)
    
def _BoolNot(a):
    return Not(a)

def _BoolXor(a, b):
    return Xor(a, b)

def _BoolImplies(a, b):
    return Implies(a, b)

def _IntLE(a, b):
    return a <= b
    
def _IntGE(a, b):
    return a >= b
    
def _IntLT(a, b):
    return a < b
    
def _IntGT(a, b):
    return a > b


def GetFunctionFromSymbol(funcSymbol):
    try:
        return{
               'bvand' : _BVAnd,
               'bvor' : _BVOr,
               'bvxor' : _BVXor,
               'bvadd' : _BVAdd,
               'bvsub' : _BVSub,
               '=' : _Equal,
               'bvmul' : _BVMul,
               'bvudiv' : _BVUdiv,
               'bvurem' : _BVUrem,
               'bvlshr' : _BVLshr,
               'bvashr' : _BVAshr,
               'bvshl' : _BVShl,
               'bvsdiv' : _BVSdiv,
               'bvsrem' : _BVSrem,
               'bvneg' : _BVNeg,
               'bvnot' : _BVNot,
               'bvugt' : _BVUgt,
               'bvuge' : _BVUge,
               'bvule' : _BVUle,
               'bvsle' : _BVSle,
               'bvult' : _BVUlt,
               'bvslt' : _BVSlt,
               'bvredor' : _BVRedor,
               '+' : _IntAdd,
               '-' : _IntSub,
               'ite' : _ITE,
               'and' : _BoolAnd,
               'or' : _BoolOr,
               'not' : _BoolNot,
               'xor' : _BoolXor,
               '<=' : _IntLE,
               '>=' : _IntGE,
               '>' : _IntGT,
               '<' : _IntLT,
               '=>' : _BoolImplies
               }[funcSymbol]
    except:
        raise Exception('Function %s not recognised by theory' % funcSymbol)
    