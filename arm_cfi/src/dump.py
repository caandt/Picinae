import lief
import struct
import argparse
from pathlib import Path

def dump_elf(path: Path):
    e: lief.ELF.Binary = lief.parse(path)

    code_segs = [x for x in e.segments if x.flags.value & 1]
    assert len(code_segs) == 1, 'more than one code segment'
    old_code = code_segs[0]

    old_a = old_code.virtual_address
    new_a = (max(x.virtual_address + x.virtual_size for x in e.segments) // 0x1000 + 2) * 0x1000
    table_a = 0xa001000
    abort_a = 0xa000000

    out = f'cfitmp/{path.stem}.bin'
    with open(out, 'wb') as f:
        f.write(struct.pack('IIII', old_a//4, new_a//4, table_a//4, abort_a//4))
        f.write(old_code.content)
    print(f'wrote {len(old_code.content) + 16} bytes to {out}')

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('binary', type=Path)

    args = parser.parse_args()

    dump_elf(args.binary)
