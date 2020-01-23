import sys
import logging
import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="INFO", logger=log)

from parser import parser, statements
from z3_backend import *

ftestcase = "testcase"

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

def write_testcase(testcase):
    with open(ftestcase, "wb") as fp:
        fp.write(testcase)

def parse_pe():
    pe = pefile.PE(ftestcase)
    return pe

if __name__ == "__main__":
    modelfile = open(sys.argv[1], "r")
    parse_file(modelfile)
    exec_statements(statements)
    solver = generate_solver()
    model = check_sat(solver)
    if model:
        testcase = generate_testcase(model)
        write_testcase(testcase)
        pefile = parse_pe()
