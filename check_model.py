import sys
import logging
import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="DEBUG", logger=log)

from parser import parser, variables, conditions


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

def gen_solver():
    solver = z3.Solver()
    for name, condition in conditions.items():
        if condition.isterminal:
            solver.assert_and_track(condition.model, name)
    return solver

def check_sat(solver):
    if solver.check().r != 1:
        log.critical("Model unsatisfiable")
        unsat_core = solver.unsat_core()
        log.critical(f"Unsat core: {unsat_core}")
        for cname in unsat_core:
            log.critical(conditions[str(cname)])
        return None
    else:
        log.info("Model satisfiable")
        log.info("Producing testcase")
        model = solver.model()
        return model
        print(model.eval(variables["HEADER"].symb))

def generate_testcase(model):
    header = variables['HEADER']
    bitvec = model.eval(header.symb)
    string_hex_rev = hex(bitvec.as_long())[2:]
    string_hex = ''.join([string_hex_rev[i:i+2]
                          for i in range(len(string_hex_rev), 0, -2)])
    test = bytes.fromhex(string_hex)
    test += b'\x00' * (header.size - len(test))
    return test

def parse_pe():
    pe = pefile.PE("test")
    return pe

if __name__ == "__main__":
    modelfile = open(sys.argv[1], "r")
    parse_file(modelfile)
    solver = gen_solver()
    model = check_sat(solver)
    if model:
        test = generate_testcase(model)
        with open("test", "wb") as fp:
            fp.write(test)
        pe = parse_pe()
        log.info(pe)
