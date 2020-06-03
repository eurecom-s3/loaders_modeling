#!/usr/bin/env python3
import sys
import logging
import coloredlogs
import z3
import pefile

log = logging.getLogger(__name__)
coloredlogs.install(level="INFO", logger=log)

from modelLang import Parser, Z3Backend, PythonBackend

if __name__ == "__main__":
    if len(sys.argv) != 3:
        log.error(f"Usage: {sys.argv[0]} <model> <executable>")
        sys.exit(1)

    modelfile = sys.argv[1]
    executable = sys.argv[2]

    with open(executable, "rb") as fp:
        content = fp.read()

    filesize = len(content)
    parser = Parser(ptype=Parser.ParserType.VALIDATOR,
                    custom_defs={"FILESIZE" : filesize})
    parser.parse_file(modelfile)
    backend = PythonBackend()
    backend.load_statements(parser.statements)

    if backend.verify(content):
        log.info("PASS")
        sys.exit(0)
    else:
        log.info("FAIL")
        sys.exit(1)
