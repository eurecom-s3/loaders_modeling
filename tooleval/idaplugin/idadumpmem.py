from idc import *
from idaapi import *
from idautils import *
import sys
from os.path import join

sys.path.append("..")
sys.path.append(".")

class ToFileStdOut(object):
    def __init__(self):
        self.outfile = open("/tmp/idaout.txt", "w")
    def write(self, text):
        self.outfile.write(text)
    def flush(self):
        self.outfile.flush()
    def isatty(self):
        return False
    def __del__(self):
        self.outfile.close()
sys.stdout = sys.stderr = ToFileStdOut()
try:

    from memdump_pb2 import MemoryDump, MemoryRegion

    if len(ARGV) < 2:
        dumpdir = "/tmp"
    else:
        dumpdir = ARGV[1]

    memdump = MemoryDump()
    for vaddr in Segments():
        memregion = memdump.regions.add()
        memregion.vaddr = vaddr
        memregion.vsize = SegEnd(vaddr) - SegStart(vaddr)
        attr = get_segm_attr(vaddr, SEGATTR_PERM)
        read = attr & SEGPERM_READ != 0
        write = attr & SEGPERM_WRITE != 0
        exc = attr & SEGPERM_EXEC != 0
        memregion.permission = "-" + ("r" if read else "-") + ("w" if write else "-") + ("x" if exc else "-")
        memregion.fsize = min(memregion.vsize, 0x10000)
        memregion.content = bytes()
        for a in xrange(vaddr, vaddr+memregion.fsize):
            if not is_loaded(a):
                break
            memregion.content += get_bytes(a, 1)
    progname = get_root_filename()
    with open(join(dumpdir, progname), "wb") as fp:
        fp.write(memdump.SerializeToString())
except Exception as e:
    print(e)
    idc.Exit(1)

idc.Exit(0)
