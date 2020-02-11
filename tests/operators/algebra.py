import z3

from parsers import Parser
from backends import *

testfile = "tests/operators/algebra.mod"

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
v4 = variables['VARD']
v5 = variables['VARE']
v6 = variables['VARF']

solver.add(input == 10)
assert(solver.check() == z3.sat)
model = solver.model()
assert(model.eval(v1).as_long() == 15)
assert(model.eval(v2).as_long() == 5)
assert(model.eval(v3).as_long() == 50)
assert(model.eval(v4).as_long() == 2)
assert(model.eval(v5).as_long() == 2)
assert(model.eval(v6).as_long() == 0)
