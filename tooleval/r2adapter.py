#!/usr/bin/env python3

import r2pipe

from tooleval import MemoryRegion, MemoryDump, FailedRelocExcetion

class Radare2Adapter(object):
    uninbyte = 0xff
    def __init__(self, path):
        self._instance = Radare2Adapter.createR2Instance(path)
        self._memdump = None

    def close(self):
        self._instance.quit()

    @staticmethod
    def createR2Instance(path):
        return r2pipe.open(path)

    @property
    def memdump(self):
        if self._memdump:
            return self._memdump

        self._memdump = MemoryDump()
        mmap = self._instance.cmdj("iSj")
        for region in mmap:
            mregion = self._memdump.regions.add()
            mregion.name = region['name']
            mregion.fsize = region['size']
            try:
                mregion.vsize = region['vsize']
                mregion.vaddr = region['vaddr']
            except:
                raise FailedRelocExcetion
            mregion.permission = region['perm']
            mregion.faddr = region['paddr']
            self._instance.cmd(f"s {hex(region['vaddr'])}")
            contentsize = mregion.vsize if mregion.vsize < 0x10000 else 0x10000
            content = bytes(self._instance.cmdj(f"pxj {hex(contentsize)}"))
            mregion.content = content
        return self._memdump

if __name__ == "__main__":
    adapter = Radare2Adapter("/home/dario/phd/loaders_modeling/lang_parser/prova/testcase_41")
    dump = adapter.memdump
