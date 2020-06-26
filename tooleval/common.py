NOTDUMPED = "NOTDUMPED"
NOTFOUND = "NOTFOUND"
def byteat(memdump, addr):
    for region in memdump.regions:
        if addr >= region.vaddr and addr < region.vaddr + region.vsize:
            if addr >= region.vaddr + len(region.content):
                return NOTDUMPED
            return region.content[region.vaddr - addr]
    return NOTFOUND

def coalesceregions(memdump):
    lastaddr = 0
    coalescedregions = []
    for region in memdump.regions:
        if region.vaddr != lastaddr:
            coalescedregions.append((region.vaddr, region.vsize))
        else:
            last = coalescedregions[-1]
            coalescedregions[-1] = (last[0], last[1] + region.vsize)
        lastaddr = region.vaddr + region.vsize
    return coalescedregions
