from cparser import *

DEFAULT_SIZES = {
    'char'      : 8,
    'short'     : 16,
    'int'       : 32,
    'long'      : 32,
    'long long' : 64
}

BASIC_TYPES = {
    'char': SimTypeNum(DEFAULT_SIZES['char'], True),
    'signed char': SimTypeNum(DEFAULT_SIZES['char'], True),
    'unsigned char': SimTypeNum(DEFAULT_SIZES['char'], False),

    'short': SimTypeNum(DEFAULT_SIZES['short'], True),
    'signed short': SimTypeNum(DEFAULT_SIZES['short'], True),
    'unsigned short': SimTypeNum(DEFAULT_SIZES['short'], False),
    'short int': SimTypeNum(DEFAULT_SIZES['short'], True),
    'signed short int': SimTypeNum(DEFAULT_SIZES['short'], True),
    'unsigned short int': SimTypeNum(DEFAULT_SIZES['short'], False),

    'int': SimTypeNum(DEFAULT_SIZES['int'], True),
    'signed int': SimTypeNum(DEFAULT_SIZES['int'], True),
    'unsigned int': SimTypeNum(DEFAULT_SIZES['int'], False),

    'long': SimTypeNum(DEFAULT_SIZES['long'], True),
    'signed long': SimTypeNum(DEFAULT_SIZES['long'], True),
    'unsigned long': SimTypeNum(DEFAULT_SIZES['long'], False),
    'long int': SimTypeNum(DEFAULT_SIZES['long'], True),
    'signed long int': SimTypeNum(DEFAULT_SIZES['long'], True),
    'unsigned long int': SimTypeNum(DEFAULT_SIZES['long'], False),

    'long long' : SimTypeNum(DEFAULT_SIZES['long long'], True),
    'signed long long': SimTypeNum(DEFAULT_SIZES['long long'], True),
    'unsigned long long': SimTypeNum(DEFAULT_SIZES['long long'], False),
    'long long int': SimTypeNum(DEFAULT_SIZES['long long'], True),
    'signed long long int': SimTypeNum(DEFAULT_SIZES['long long'], True),
    'unsigned long long int': SimTypeNum(DEFAULT_SIZES['long long'], False),

    'float': SimTypeFloat(),
    'double': SimTypeDouble(),
    'void': SimTypeBottom(),
}

OTHER_TYPES = {
    '__int64'   : BASIC_TYPES['long long'],
    'BYTE'      : BASIC_TYPES['unsigned char'],
    'CHAR'      : BASIC_TYPES['char'],
    'DWORD'     : BASIC_TYPES['long'],
    'DWORD32'   : BASIC_TYPES['int'],
    'DWORD64'   : BASIC_TYPES['long'],
    'INT'       : BASIC_TYPES['int'],
    'INT8'      : BASIC_TYPES['int'],
    'INT16'     : BASIC_TYPES['short'],
    'INT32'     : BASIC_TYPES['int'],
    'INT64'     : BASIC_TYPES['long long'],
    'LONG'      : BASIC_TYPES['long'],
    'LONGLONG'  : BASIC_TYPES['long long'],
    'UCHAR'     : BASIC_TYPES['unsigned char'],
    'UINT'      : BASIC_TYPES['unsigned int'],
    'UINT8'     : BASIC_TYPES['unsigned int'],
    'UINT16'    : BASIC_TYPES['unsigned short'],
    'UINT32'    : BASIC_TYPES['unsigned int'],
    'UINT64'    : BASIC_TYPES['unsigned long long'],
    'ULONG'     : BASIC_TYPES['unsigned long'],
    'ULONGLONG' : BASIC_TYPES['unsigned long long'],
    'USHORT'    : BASIC_TYPES['unsigned short'],
    'WORD'      : BASIC_TYPES['unsigned short']
}

update_types({**BASIC_TYPES, **OTHER_TYPES})
