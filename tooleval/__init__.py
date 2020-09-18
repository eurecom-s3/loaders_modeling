from .common import byteat, NOTDUMPED, NOTFOUND, coalesceregions, FailedRelocExcetion
from .memdump_pb2 import MemoryRegion, MemoryDump
from .r2adapter import Radare2Adapter
from .winadapter import WindowsAdapter
from .ghidraadapter import GhidraAdapter
from .idaadapter import IDAAdapter
TOOLADAPTERS = {'radare2': Radare2Adapter,
                'ghidra': GhidraAdapter,
                'ida': IDAAdapter}
