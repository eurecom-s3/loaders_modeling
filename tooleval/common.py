NOTDUMPED = "NOTDUMPED"
NOTFOUND = "NOTFOUND"

class FailedRelocExcetion(Exception):
    pass

def byteat(memdump, addr):
    for region in memdump.regions:
        if addr >= region.vaddr and addr < region.vaddr + region.vsize:
            if addr >= region.vaddr + len(region.content):
                return NOTDUMPED
            return region.content[addr - region.vaddr]
    return NOTFOUND

def permissionsat(memdump, addr):
    for region in memdump.regions:
        if addr >= region.vaddr and addr < region.vaddr + region.vsize:
            return region.permission
    return NOTFOUND

def coalesceregions(memdump):
    lastaddr = -1
    coalescedregions = []
    for region in memdump.regions:
        if region.vaddr != lastaddr:
            coalescedregions.append((region.vaddr, region.vsize))
        else:
            last = coalescedregions[-1]
            coalescedregions[-1] = (last[0], last[1] + region.vsize)
        lastaddr = region.vaddr + region.vsize
    return coalescedregions
