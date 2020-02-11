import z3

from parsers import Parser
from backends import *

testfile = "tests/operators/bitwise.mod"

def parse_file(f):
    lines = f.readlines()
    cnt = 0
    for s in lines:
        cnt += 1
        if not s: continue
        log.info(f"Line {cnt}: {s}")
        result = parser.parse(s)
        if result:
            print(result)

parser = Parser()
parser.parse_file(testfile)
exec_statements(parser.statements)
solver = generate_solver()
input = variables['VARIABLE']
v1 = variables['VARA']
v2 = variables['VARB']
v3 = variables['VARC']

solver.add(input == 0xdeadbeef)
assert(solver.check() == z3.sat)
model = solver.model()
assert(model.eval(v1).as_long() == 0x11001)
assert(model.eval(v2).as_long() == 0xdfadbeef)
assert(model.eval(v3).as_long() == 0x21524110)
