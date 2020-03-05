#!/usr/bin/env python3
import argparse
import sys
import os.path as path
import logging
from functools import reduce

import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="INFO", logger=log)

from parsers import Parser
from backends import Z3Backend

def write_testcase(testcase, fout):
    with open(fout, "wb") as fp:
        fp.write(testcase)

if __name__ == "__main__":
    argparser = argparse.ArgumentParser(description="Interpret models and generate testcases")
    argparser.add_argument('--asserts', '-A', action="append",
                           metavar="model", type=str, nargs="+",
                           help="Model to assert")
    argparser.add_argument('--negates', '-N', action="append",
                           metavar="model", type=str, nargs="*",
                           default=[],
                           help="Model to negate")
    argparser.add_argument('--out', '-O', action="store",
                           metavar="outfile", type=str, nargs=1,
                           default="testcase",
                           help="Output file for testcase")
    argparser.add_argument('--var', '-V', action="store",
                           metavar="varaible", type=str, nargs=1,
                           default="HEADER",
                           help="Variable in the model to use for the testcase")

    args = argparser.parse_args()
    asserts = reduce(lambda x,y: x | {*y}, args.asserts, set())
    negates = reduce(lambda x,y: x | {*y}, args.negates, set())
    outfile = args.out
    voi = args.var

    z3_models_assert = []
    z3_models_negate = []
    for model in [*asserts, *negates]:
        modelname = path.basename(model)
        parser = Parser()
        parser.parse_file(model)
        backend = Z3Backend(name=modelname, voi=voi)
        backend.exec_statements(parser.statements)
        if model in asserts:
            z3_models_assert.append(backend)
        else:
            z3_models_negate.append(backend)

    backend = z3_models_assert[0]
    for b in z3_models_assert[1:]:
        backend &= b

    for b in z3_models_negate:
        backend &= ~b

    solver = backend.solver
    model = backend.model
    if model:
        testcase = backend.generate_testcase()
        write_testcase(testcase, outfile)
