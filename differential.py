#!/usr/bin/env python3
import argparse
import sys
import os.path as path
import logging
from functools import reduce
from itertools import product, combinations

import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="INFO", logger=log)

from parsers import Parser
from backends import Z3Backend

def gen_constraint_name(model, cond):
    return f"{model.name}_{cond}"

def create_constraints_db(models):
    ret = {}
    for model in models:
        for name, cond in model.terminal_conditions.items():
            cname = gen_constraint_name(model, name)
            ret[cname] = cond
    return ret

def write_testcase(testcase, constraints, fout):
    with open(fout, "wb") as fp:
        fp.write(testcase)
    with open(f"{fout}.constraints", "w") as fp:
        for name in constraints:
            fp.write(f"{name}\n")

def generate(z3_models_assert, z3_models_negate, z3_model_support=None):
    backend = z3_models_assert[0]
    for b in z3_models_assert[1:]:
        backend &= b

    if z3_model_support:
        backend &= z3_model_support

    for b in z3_models_negate:
        backend &= ~b

    solver = backend.solver
    model = backend.model
    testcase = backend.generate_testcase() if model else None
    return model, testcase

def find_violations(model, z3_models_negate):
    ret = set()
    for mn in z3_models_negate:
        for name, cond in mn.terminal_conditions.items():
            if not model.eval(cond):
                model_name = gen_constraint_name(mn, name)
                ret.add(model_name)
    return ret

def next_iteration(violated_constraints, violated_once, processed, to_process,
                   constraints_db):
    if len(violated_once) != len(violated_once | violated_constraints):
        log.critical(f"New Constraints found! {violated_constraints - violated_once}")
        violated_once |= violated_constraints
        all_subsets = set()
        violated_once_sorted = sorted(violated_once)
        for i in range(1, len(violated_once)+1):
            all_subsets |= set(combinations(violated_once_sorted, i))

        new_subsets = all_subsets - processed
        to_process.extend(new_subsets)

    while len(to_process) > 0:
        candidate = to_process.pop(0)
        if candidate not in processed:
            break
    else:
        return None

    processed.add(candidate)
    log.critical(f"{candidate} chosen")
    z3_model_support = Z3Backend(name="suppport")
    for constr in candidate:
        z3constr = constraints_db[constr]
        z3_model_support.terminal_conditions[constr] = z3constr
        z3_model_support.conditions[constr] = z3constr

    return z3_model_support

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
                           metavar="outfile", type=str,
                           default="testcase",
                           help="Output file for testcase")
    argparser.add_argument('--var', '-V', action="store",
                           metavar="variable", type=str, nargs=1,
                           default="HEADER",
                           help="Variable in the model to use for the testcase")
    argparser.add_argument('--size', '-B', action="store", metavar="bytes",
                          type=int, default=None,
                          help="Size in bytes of the testcase to generate")
    argparser.add_argument('--define', '-D', action="store", metavar="define",
                           type=lambda x: (x.split(":")[0],
                                           int(x.split(":")[1])),
                           nargs="*",
                           help="Overwrite constant definition")

    args = argparser.parse_args()
    asserts = reduce(lambda x,y: x | {*y}, args.asserts, set())
    negates = reduce(lambda x,y: x | {*y}, args.negates, set())
    outfile = args.out
    voi = args.var
    size = args.size
    defs = dict(args.define) if args.define else {}

    Z3Backend.print_unsat = False
    z3_models_assert = []
    z3_models_negate = []
    for model in asserts:
        modelname = path.basename(model)
        parser = Parser(ptype=Parser.ParserType.GENERATOR, input_size=size,
                        custom_defs=defs)
        parser.parse_file(model)
        backend = Z3Backend(name=modelname, voi=voi)
        backend.exec_statements(parser.statements)
        z3_models_assert.append(backend)
    for model in negates:
        modelname = path.basename(model)
        parser = Parser(ptype=Parser.ParserType.VALIDATOR, input_size=size,
                        custom_defs=defs)
        parser.parse_file(model)
        backend = Z3Backend(name=modelname, voi=voi)
        backend.exec_statements(parser.statements)
        z3_models_negate.append(backend)


    constraints_db = create_constraints_db((*z3_models_assert,
                                            *z3_models_negate))
    to_process = []
    processed = set()
    violated_once = set()
    current_constraints = ()
    z3_model_support = None
    iteration = 0
    while True:
        violated_constraints = set()
        model, testcase = generate(z3_models_assert, z3_models_negate,
                                   z3_model_support)
        if model:
            #### Find violated constraints
            violated_constraints = find_violations(model, z3_models_negate)
            log.critical(f"Violated Constraints: {violated_constraints}")
            #### Write testcase
            write_testcase(testcase, violated_constraints,
                           f"{outfile}_{iteration}")

        z3_model_support = next_iteration(violated_constraints,
                                          violated_once,
                                          processed,
                                          to_process,
                                          constraints_db)
        if not z3_model_support:
            break
        iteration += 1
