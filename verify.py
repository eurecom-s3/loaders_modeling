#!/usr/bin/env python3
import sys
import logging
import coloredlogs
import z3
import pefile

from argparse import ArgumentParser

log = logging.getLogger(__name__)
coloredlogs.install(level="NOTSET", logger=log)

from modelLang import Parser, Z3Backend, PythonBackend

if __name__ == "__main__":
    argpar = ArgumentParser(description='Evaluate model precision')
    argpar.add_argument('model', type=str, help='Loader model')
    argpar.add_argument('executable', type=str, help='File to verify')
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
    executable = args.executable
    if args.logLevel:
        logging.getLogger().setLevel(args.logLevel)
    with open(executable, "rb") as fp:
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
        log.info("PASS")
        sys.exit(0)
    else:
        log.info("FAIL")
        sys.exit(1)
