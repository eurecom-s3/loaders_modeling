#!/usr/bin/env python3

from tooleval import MemoryRegion, MemoryDump

class WindowsAdapter(object):
    def __init__(self, path):
        self._file = open(path, 'rb')
        self._memdump = None

    def close(self):
        self._file.close()

    def load(self):
        self._memdump = MemoryDump()
        self._memdump.ParseFromString(self._file.read())

    @property
    def memdump(self):
        if not self._memdump:
            self.load()
        return self._memdump

if __name__ == "__main__":
    adapter = WindowsAdapter("/home/dario/VirtualBox VMs/winxp/shared/mydumps/testcase_35.exe.dump")
    dump = adapter.memdump
    print(dump)

