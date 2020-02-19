#!/usr/bin/env python3

import logging
import coloredlogs

class Test():
    testfile = ""

    @staticmethod
    def run():
        raise NotImplementedError


if __name__ == "__main__":
    def test(c):
        name = c.__name__
        log.info(f"Running {name}")
        try:
            c.run()
        except AssertionError as e:
            log.error(f"{name} failed with error {e}")
        else:
            log.info(f"{name} succeded")
        
    log = logging.getLogger(__name__)
    coloredlogs.install(level="INFO", logger=log)
    from loops import VLoopTest
    from operators import BitwiseTest, AlgebraTest

    test(BitwiseTest)
    test(AlgebraTest)
    test(VLoopTest)
