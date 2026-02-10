from os import chmod
import array
import argparse
import lief
from pathlib import Path

ABORT_CODE = Path('src/abort/abort.bin').read_bytes()

RX = lief.ELF.Segment.FLAGS(0b101)
RO = lief.ELF.Segment.FLAGS(0b100)

def instrument_elf(path: Path, out: Path, abort_code: bytes = ABORT_CODE):
    e: lief.ELF.Binary = lief.parse(path)

    code_segs = [x for x in e.segments if x.flags.value & 1]
    assert len(code_segs) == 1, 'more than one code segment'
    old_code = code_segs[0]

    old_a = old_code.virtual_address
    new_a = (max(x.virtual_address + x.virtual_size for x in e.segments) // 0x1000 + 2) * 0x1000
    table_a = 0xa001000
    abort_a = 0xa000000

    print('adding segments')
    new_seg = lief.ELF.Segment()
    table_seg = lief.ELF.Segment()
    abort_seg = lief.ELF.Segment()

    old_code.flags = RO

    new_seg.content = memoryview(Path(f'cfitmp/{path.stem}.txt.bin').read_bytes())
    new_seg.virtual_address = new_a
    new_seg.flags = RX
    new_seg.type = lief.ELF.Segment.TYPE.LOAD

    table_seg.content = memoryview(Path(f'cfitmp/{path.stem}.dat.bin').read_bytes())
    table_seg.virtual_address = table_a
    table_seg.flags = RO
    table_seg.type = lief.ELF.Segment.TYPE.LOAD

    abort_seg.content = memoryview(abort_code)
    abort_seg.virtual_address = abort_a
    abort_seg.flags = RX
    abort_seg.type = lief.ELF.Segment.TYPE.LOAD

    i_s = array.array('I')
    i_s.frombytes(Path(f'cfitmp/{path.stem}.i_s.bin').read_bytes())
    i2i = lambda x: i_s[x - old_a//4] if old_a <= x * 4 < old_a + old_code.virtual_size else x

    e.add(new_seg)
    e.add(table_seg)
    e.add(abort_seg)

    e.header.entrypoint = i2i(e.entrypoint//4) * 4

    print('updating symbols')
    for s in e.symbols:
        if s.section and s.section.name == '.text':
            sa = i2i(s.value//4)*4
            s.value = sa
            s.size = i2i((s.value+s.size)//4)*4-sa
    txt = e.get_section('.text')
    txt.virtual_address = i2i(txt.virtual_address//4)*4

    for section in e.sections:
        if lief.ELF.Section.FLAGS.COMPRESSED in section.flags_list:
            section.remove(lief.ELF.Section.FLAGS.COMPRESSED)

    e.write(str(out))
    chmod(out, 0o755)
    print(f'created binary {out}')

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('input', type=Path)
    parser.add_argument('-o', '--output', type=Path)

    args = parser.parse_args()

    if args.output is None:
        args.output = args.input.with_name('rr' + args.input.name)
    instrument_elf(args.input, args.output)
