#!/usr/bin/env python3
import sys
import logging
import coloredlogs
import z3
import pefile

from argparse import ArgumentParser
from pathlib import Path
from functools import partial
from multiprocessing import Pool
from progressbar import progressbar

log = logging.getLogger(__name__)
coloredlogs.install(level="NOTSET", logger=log)

from modelLang import Parser, Z3Backend, PythonBackend


def verify(modelfile, executable):
    with executable.open("rb") as fp:
        content = fp.read()

    filesize = len(content)
    parser = Parser(ptype=Parser.ParserType.VALIDATOR,
                    custom_defs={"FILESIZE" : filesize})
    parser.parse_file(modelfile)
    backend = engine()

    if args.disable_log:
        backend.log.setLevel(100)
    backend.load_statements(parser.statements)
    if backend.verify(content):
        return (executable, None)
    else:
        return (executable, backend._last_fail)

if __name__ == "__main__":
    argpar = ArgumentParser(description='Evaluate model precision')
    argpar.add_argument('model', type=str, help='Loader model')
    argpar.add_argument('directory', type=str,
                        help='Path to dataset to verify')
    argpar.add_argument('output', type=str,
                        help='Path to output')
    argpar.add_argument('--logLevel', '-l', type=str, default=None,
                        help="Log verbosity")
    argpar.add_argument('--disable-log', '-D', default=False,
                        action='store_true', help="Disable logging")
    argpar.add_argument('--z3-backend', '-Z', default=False,
                        action="store_true", help="Enable z3 backend")

    args = argpar.parse_args()
    engine = PythonBackend
    if args.z3_backend:
        engine = Z3Backend

    modelfile = args.model
    directory = Path(args.directory)

    if not directory.is_dir():
        log.error("<directory> must be a directoy")
        sys.exit(-1)

    samples = list(directory.iterdir())

    if args.logLevel:
        logging.getLogger().setLevel(args.logLevel)

    pool = Pool()
    results = {x.name: y for x, y in progressbar(pool.imap(partial(verify,
                                                                   modelfile),
                                                           samples),
                                                 max_value=len(samples))}
    pool.close()
    pool.terminate()
    success = sum(1 for x in results.values() if not x)
    with open(args.output, "w") as fp:
        fp.write(f"Success: {success}\n")
        for n, c in results.items():
            if not c:
                continue
            fp.write(f"{n} {c}\n")
