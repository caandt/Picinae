import sys
import array
a = array.array('I')
a.fromlist([int(x.strip(), 16)//4 for x in sys.stdin if x])
with open(sys.argv[1], 'wb') as f:
    f.write(a.tobytes())
print(f'wrote {len(a) * 4} bytes to {sys.argv[1]}')
