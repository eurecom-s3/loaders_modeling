#define IMAGE_NUMBEROF_DIRECTORY_ENTRIES    16
#define IMAGE_SIZEOF_SHORT_NAME              8
#define IMAGE_SIZEOF_SECTION_HEADER          40
#define IMAGE_SIZEOF_FILE_HEADER             20

typedef struct _IMAGE_DOS_HEADER {
  USHORT e_magic;
  USHORT e_cblp;
  USHORT e_cp;
  USHORT e_crlc;
  USHORT e_cparhdr;
  USHORT e_minalloc;
  USHORT e_maxalloc;
  USHORT e_ss;
  USHORT e_sp;
  USHORT e_csum;
  USHORT e_ip;
  USHORT e_cs;
  USHORT e_lfarlc;
  USHORT e_ovno;
  USHORT e_res[4];
  USHORT e_oemid;
  USHORT e_oeminfo;
  USHORT e_res2[10];
  LONG e_lfanew;
} IMAGE_DOS_HEADER, *PIMAGE_DOS_HEADER;

typedef struct _IMAGE_EXPORT_DIRECTORY {
  ULONG Characteristics;
  ULONG TimeDateStamp;
  USHORT MajorVersion;
  USHORT MinorVersion;
  ULONG Name;
  ULONG Base;
  ULONG NumberOfFunctions;
  ULONG NumberOfNames;
  ULONG AddressOfFunctions;
  ULONG AddressOfNames;
  ULONG AddressOfNameOrdinals;
} IMAGE_EXPORT_DIRECTORY, *PIMAGE_EXPORT_DIRECTORY;

typedef struct _IMAGE_RESOURCE_DATA_ENTRY {
  ULONG OffsetToData;
  ULONG Size;
  ULONG CodePage;
  ULONG Reserved;
} IMAGE_RESOURCE_DATA_ENTRY, *PIMAGE_RESOURCE_DATA_ENTRY;

typedef struct {
  ULONG Size;
  ULONG TimeDateStamp;
  USHORT MajorVersion;
  USHORT MinorVersion;
  ULONG GlobalFlagsClear;
  ULONG GlobalFlagsSet;
  ULONG CriticalSectionDefaultTimeout;
  ULONG DeCommitFreeBlockThreshold;
  ULONG DeCommitTotalFreeThreshold;
  ULONG LockPrefixTable;
  ULONG MaximumAllocationSize;
  ULONG VirtualMemoryThreshold;
  ULONG ProcessHeapFlags;
  ULONG ProcessAffinityMask;
  USHORT CSDVersion;
  USHORT Reserved1;
  ULONG EditList;
  ULONG SecurityCookie;
  ULONG SEHandlerTable;
  ULONG SEHandlerCount;
} IMAGE_LOAD_CONFIG_DIRECTORY32, *PIMAGE_LOAD_CONFIG_DIRECTORY32;

typedef struct {
  ULONG Size;
  ULONG TimeDateStamp;
  USHORT MajorVersion;
  USHORT MinorVersion;
  ULONG GlobalFlagsClear;
  ULONG GlobalFlagsSet;
  ULONG CriticalSectionDefaultTimeout;
  ULONGLONG DeCommitFreeBlockThreshold;
  ULONGLONG DeCommitTotalFreeThreshold;
  ULONGLONG LockPrefixTable;
  ULONGLONG MaximumAllocationSize;
  ULONGLONG VirtualMemoryThreshold;
  ULONGLONG ProcessAffinityMask;
  ULONG ProcessHeapFlags;
  USHORT CSDVersion;
  USHORT Reserved1;
  ULONGLONG EditList;
  ULONGLONG SecurityCookie;
  ULONGLONG SEHandlerTable;
  ULONGLONG SEHandlerCount;
} IMAGE_LOAD_CONFIG_DIRECTORY64, *PIMAGE_LOAD_CONFIG_DIRECTORY64;

typedef struct _IMAGE_SECTION_HEADER {
  UCHAR Name[IMAGE_SIZEOF_SHORT_NAME];
  union {
    ULONG PhysicalAddress;
    ULONG VirtualSize;
  } Misc;
  ULONG VirtualAddress;
  ULONG SizeOfRawData;
  ULONG PointerToRawData;
  ULONG PointerToRelocations;
  ULONG PointerToLinenumbers;
  USHORT NumberOfRelocations;
  USHORT NumberOfLinenumbers;
  ULONG Characteristics;
} IMAGE_SECTION_HEADER, *PIMAGE_SECTION_HEADER;

typedef struct _IMAGE_FILE_HEADER {
  USHORT Machine;
  USHORT NumberOfSections;
  ULONG TimeDateStamp;
  ULONG PointerToSymbolTable;
  ULONG NumberOfSymbols;
  USHORT SizeOfOptionalHeader;
  USHORT Characteristics;
} IMAGE_FILE_HEADER, *PIMAGE_FILE_HEADER;

typedef struct _IMAGE_DATA_DIRECTORY {
  ULONG VirtualAddress;
  ULONG Size;
} IMAGE_DATA_DIRECTORY, *PIMAGE_DATA_DIRECTORY;

typedef struct _IMAGE_OPTIONAL_HEADER {
  USHORT Magic;
  UCHAR MajorLinkerVersion;
  UCHAR MinorLinkerVersion;
  ULONG SizeOfCode;
  ULONG SizeOfInitializedData;
  ULONG SizeOfUninitializedData;
  ULONG AddressOfEntryPoint;
  ULONG BaseOfCode;
  ULONG BaseOfData;
  ULONG ImageBase;
  ULONG SectionAlignment;
  ULONG FileAlignment;
  USHORT MajorOperatingSystemVersion;
  USHORT MinorOperatingSystemVersion;
  USHORT MajorImageVersion;
  USHORT MinorImageVersion;
  USHORT MajorSubsystemVersion;
  USHORT MinorSubsystemVersion;
  ULONG Win32VersionValue;
  ULONG SizeOfImage;
  ULONG SizeOfHeaders;
  ULONG CheckSum;
  USHORT Subsystem;
  USHORT DllCharacteristics;
  ULONG SizeOfStackReserve;
  ULONG SizeOfStackCommit;
  ULONG SizeOfHeapReserve;
  ULONG SizeOfHeapCommit;
  ULONG LoaderFlags;
  ULONG NumberOfRvaAndSizes;
  IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
} IMAGE_OPTIONAL_HEADER32, *PIMAGE_OPTIONAL_HEADER32;

typedef struct _IMAGE_ROM_OPTIONAL_HEADER {
  USHORT Magic;
  UCHAR MajorLinkerVersion;
  UCHAR MinorLinkerVersion;
  ULONG SizeOfCode;
  ULONG SizeOfInitializedData;
  ULONG SizeOfUninitializedData;
  ULONG AddressOfEntryPoint;
  ULONG BaseOfCode;
  ULONG BaseOfData;
  ULONG BaseOfBss;
  ULONG GprMask;
  ULONG CprMask[4];
  ULONG GpValue;
} IMAGE_ROM_OPTIONAL_HEADER, *PIMAGE_ROM_OPTIONAL_HEADER;

typedef struct _IMAGE_OPTIONAL_HEADER64 {
  USHORT Magic;
  UCHAR MajorLinkerVersion;
  UCHAR MinorLinkerVersion;
  ULONG SizeOfCode;
  ULONG SizeOfInitializedData;
  ULONG SizeOfUninitializedData;
  ULONG AddressOfEntryPoint;
  ULONG BaseOfCode;
  ULONGLONG ImageBase;
  ULONG SectionAlignment;
  ULONG FileAlignment;
  USHORT MajorOperatingSystemVersion;
  USHORT MinorOperatingSystemVersion;
  USHORT MajorImageVersion;
  USHORT MinorImageVersion;
  USHORT MajorSubsystemVersion;
  USHORT MinorSubsystemVersion;
  ULONG Win32VersionValue;
  ULONG SizeOfImage;
  ULONG SizeOfHeaders;
  ULONG CheckSum;
  USHORT Subsystem;
  USHORT DllCharacteristics;
  ULONGLONG SizeOfStackReserve;
  ULONGLONG SizeOfStackCommit;
  ULONGLONG SizeOfHeapReserve;
  ULONGLONG SizeOfHeapCommit;
  ULONG LoaderFlags;
  ULONG NumberOfRvaAndSizes;
  IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
} IMAGE_OPTIONAL_HEADER64, *PIMAGE_OPTIONAL_HEADER64;
