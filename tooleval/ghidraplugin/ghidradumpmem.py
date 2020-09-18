prog = getCurrentProgram()
name = prog.getName()

print(name)

fname = "/tmp/ghidradumps/" + name

dumpMemory(fname)
