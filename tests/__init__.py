#!/usr/bin/env python3
import logging
import coloredlogs

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
    from loops import VLoopTest, ConditionalLoopTest
    from operators import (BitwiseTest, AlgebraTest, AlignmentTest,
                           StringCompareTest, OverflowTest)
    from statements import (FromFileTest, OptimizationTest,
                            ConditionalAssignmentTest)
    from functional import PositiveCombinationTest, NegativeCombinationTest

    test(BitwiseTest)
    test(AlgebraTest)
    test(AlignmentTest)
    test(StringCompareTest)
    test(OverflowTest)
    test(VLoopTest)
    test(ConditionalLoopTest)
    test(FromFileTest)
    test(OptimizationTest)
    test(ConditionalAssignmentTest)
    test(PositiveCombinationTest)
    test(NegativeCombinationTest)
