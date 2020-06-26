#!/usr/bin/env python3
import argparse
import sys
import os.path as path
import logging
from functools import reduce
from itertools import product

import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="INFO", logger=log)

from modelLang import Parser, Z3Backend

def write_testcase(testcase, outdir, cs, n):
    testcasename = path.join(outdir, f"testcase_{n}")
    conditionsname = path.join(outdir, f"testcase_{n}.cond")
    with open(testcasename, "wb") as fp:
        fp.write(testcase)
    with open(conditionsname, "w") as fp:
        for c in cs:
            fp.write(f"{c[0][0]} {c[1]}\n")

def update_blacklist(unsat, cs, blacklist):
    entry = dict()
    for cname in unsat:
        for c in cs:
            if c[0][0] == str(cname):
                entry[c[0][0]] = c[1]
                break
        else:
            log.warning(f"Could not find {cname} among the constraints")
            return
    blacklist.append(entry)

def isblacklisted(cs, blacklist):
    for b in blacklist:
        tmp = {cname: False for cname in b}
        for cname, value in b.items():
            for ((cname2, _), value2) in cs:
                if (cname, value) == (cname2, value2):
                    tmp[cname] = True
        if all(tmp.values()):
            return True
    return False

if __name__ == "__main__":
    argparser = argparse.ArgumentParser(description="Explore all combinations of non-terminal conditions to generate different testcases.")
    argparser.add_argument('--models', '-M', action="append",
                           metavar="model", type=str, nargs="+",
                           help="Models to explore")
    argparser.add_argument('--supports', '-S', action="append",
                           metavar="model", type=str, nargs="*", default=[],
                           help="Other models to assert")
    argparser.add_argument('--outdir', '-O', action="store",
                           metavar="outfile", type=str,
                           default="testcase",
                           help="Output directory file for testcases")
    argparser.add_argument('--size', '-B', action="store", metavar="bytes",
                          type=int, default=None,
                          help="Size in bytes of the testcase to generate")
    argparser.add_argument('--define', '-D', action="store", metavar="define",
                           type=lambda x: (x.split(":")[0],
                                           int(x.split(":")[1])),
                           nargs="*",
                           help="Overwrite constant definition")
    argparser.add_argument('--var', '-V', action="store",
                           metavar="variable", type=str, nargs=1,
                           default="HEADER",
                           help="Variable in the model to use for the testcase")

    args = argparser.parse_args()
    inputs = reduce(lambda x,y: x | {*y}, args.models, set())
    supports = reduce(lambda x,y: x | {*y}, args.supports, set())
    outdir = args.outdir
    size = args.size
    voi = args.var
    defs = dict(args.define) if args.define else {}

    Z3Backend.print_unsat = False
    z3models = []
    for model in inputs:
        modelname = path.basename(model)
        parser = Parser(ptype=Parser.ParserType.DIFFERENTIAL_ASSERT,
                        input_size=size,
                        custom_defs=defs)
        parser.parse_file(model)
        backend = Z3Backend(name=modelname, voi=voi)
        backend.exec_statements(parser.statements)
        z3models.append(backend)

    backend = z3models[0]
    for m in z3models[1:]:
        backend &= m

    z3supports = []
    for model in supports:
        modelname = path.basename(model)
        parser = Parser(ptype=Parser.ParserType.DIFFERENTIAL_ASSERT,
                        input_size=size,
                        custom_defs=defs)
        parser.parse_file(model)
        tmp = Z3Backend(name=modelname, voi=voi)
        tmp.exec_statements(parser.statements)
        z3supports.append(tmp)

    for m in z3supports:
        backend &= m

    nterminal_conds = list(reduce(lambda x, y: x+y,
                                  [[(x, m.conditions[x])
                                    for x in (m.conditions.keys()
                                              - m.terminal_conditions.keys())
                                  ] for m in z3models],
                                  []))
    nconds = len(nterminal_conds)
    log.info(f"{nconds} found. Generating {2**nconds} testcases")
    alltf = product([True, False], repeat=nconds)

    n = 0
    blacklist = []
    for tfs in alltf:
        # cs = [((name, z3cond), bool), ... ]
        cs = list(zip(nterminal_conds, tfs))
        if isblacklisted(cs, blacklist):
            log.warning("Combination is known to be unsat")
            continue

        support = Z3Backend()
        for c in cs:
            if c[1]:
                support.terminal_conditions[c[0][0]] = c[0][1]
            else:
                support.terminal_conditions[c[0][0]] = z3.Not(c[0][1])
        if not support.model:
            log.warning("Support model is unsat. Checking the unsat core and discarinding conflitting constraints.")
            unsat = support.solver.unsat_core()
            update_blacklist(unsat, cs, blacklist)
            continue

        tmpbackend = backend & support
        tmpmodel = tmpbackend.model
        if tmpmodel:
            n += 1
            testcase = tmpbackend.generate_testcase()
            write_testcase(testcase, outdir, cs, n)
