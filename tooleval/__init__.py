from .memdump_pb2 import MemoryRegion, MemoryDump
from .r2adapter import Radare2Adapter
from .winadapter import WindowsAdapter
from .common import byteat, NOTDUMPED, NOTFOUND, coalesceregions
TOOLADAPTERS = {'radare2': Radare2Adapter}
