all: memdump.pb.cc memdump_pb2.py ghidra/program/flatapi/Memdump.java

memdump.pb.cc: memdump.proto
	protoc $< --cpp_out=.

memdump_pb2.py: memdump.proto
	protoc $< --python_out=.

ghidra/program/flatapi/Memdump.java: memdump.proto
	protoc $< --java_out=.

.PHONY: all
