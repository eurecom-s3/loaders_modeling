from collections import namedtuple

Entry = namedtuple('Entry', ['name', 'size', 'vsize',
                             'perm', 'paddr', 'vaddr'])
class MemoryMap(list):
    def __init__(self):
        super().__init__(self)

    def append(self, obj):
        if type(obj) != Entry:
            raise TypeError
        super().append(obj)

class MemoryDump(dict):
    def __init__(self):
        super().__init__(self)

    def __setitem__(self, key, value):
        if type(key) != Entry:
            raise TypeError
        super().__setitem__(key, value)
