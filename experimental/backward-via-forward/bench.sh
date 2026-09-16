#!/bin/bash
export MORK=~/Work/TrueAGI/MORK/target/release/mork
export DIR=~/Work/TrueAGI/chaining/experimental/backward-via-forward

python3 -c "
import os
DIR = os.environ['DIR']
def make_imim1(input_path, output_path, jarr_marker, imim1_target):
    with open(input_path, 'rb') as f:
        content = f.read()
    new = content.replace(jarr_marker, imim1_target)
    with open(output_path, 'wb') as f:
        f.write(new)

# obfc-xp.mm2 uses c: wrapper
make_imim1(f'{DIR}/obfc-xp.mm2', f'{DIR}/obfc-xp-imim1.mm2',
           b'(target 13 (c: (\xe2\x86\x92 (\xe2\x86\x92 (\xe2\x86\x92 \xf0\x9d\x9c\x91 \xf0\x9d\x9c\x93) \xf0\x9d\x9c\x92) (\xe2\x86\x92 \xf0\x9d\x9c\x93 \xf0\x9d\x9c\x92)) \$x))',
           b'(target 15 (c: (\xe2\x86\x92 (\xe2\x86\x92 \xf0\x9d\x9c\x91 \xf0\x9d\x9c\x93) (\xe2\x86\x92 (\xe2\x86\x92 \xf0\x9d\x9c\x93 \xf0\x9d\x9c\x92) (\xe2\x86\x92 \xf0\x9d\x9c\x91 \xf0\x9d\x9c\x92))) \$x))')
# obfc-xp-fast.mm2 uses C wrapper
make_imim1(f'{DIR}/obfc-xp-fast.mm2', f'{DIR}/obfc-xp-fast-imim1.mm2',
           b'(target 13 (C (\xe2\x86\x92 (\xe2\x86\x92 (\xe2\x86\x92 \xf0\x9d\x9c\x91 \xf0\x9d\x9c\x93) \xf0\x9d\x9c\x92) (\xe2\x86\x92 \xf0\x9d\x9c\x93 \xf0\x9d\x9c\x92)) \$x))',
           b'(target 15 (C (\xe2\x86\x92 (\xe2\x86\x92 \xf0\x9d\x9c\x91 \xf0\x9d\x9c\x93) (\xe2\x86\x92 (\xe2\x86\x92 \xf0\x9d\x9c\x93 \xf0\x9d\x9c\x92) (\xe2\x86\x92 \xf0\x9d\x9c\x91 \xf0\x9d\x9c\x92))) \$x))')
print('Generated imim1 versions')
"

bench_one() {
    local file="$1"
    local label="$2"
    local times=""
    for i in 1 2 3; do
        local t=$(/usr/bin/time -f "%e" $MORK run "$file" --steps 1000000000 2>&1 > /dev/null)
        times="$times $t"
    done
    echo "$label:$times"
}

echo "=== Benchmark: obfc-xp.mm2 vs obfc-xp-fast.mm2 ==="
echo
echo "jarr (size=13):"
bench_one "$DIR/obfc-xp.mm2" "  obfc-xp.mm2      "
bench_one "$DIR/obfc-xp-fast.mm2" "  obfc-xp-fast.mm2 "
echo
echo "imim1 (size=15):"
bench_one "$DIR/obfc-xp-imim1.mm2" "  obfc-xp.mm2      "
bench_one "$DIR/obfc-xp-fast-imim1.mm2" "  obfc-xp-fast.mm2 "
