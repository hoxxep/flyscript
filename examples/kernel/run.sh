#!/bin/sh
# Builds the kernel and runs it on QEMU's `virt` board: `examples/kernel/run.sh [compiler.js]`.
# Needs clang, ld.lld and qemu-system-aarch64.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
compiler=${1:-$root/selfhost/seed.js}
out=$(mktemp -d)
node --stack-size=65500 "$compiler" "$here/kernel.fly" "$out/kernel.c" "$root" --freestanding
flags="-target aarch64-none-elf -std=gnu11 -ffreestanding -fno-stack-protector -mcpu=cortex-a72 -mstrict-align -O2 -w"
clang $flags -c "$out/kernel.c" -o "$out/kernel.o"
clang $flags -c "$here/boot.S" -o "$out/boot.o"
ld.lld -T "$here/linker.ld" "$out/boot.o" "$out/kernel.o" -o "$out/kernel.elf"
qemu-system-aarch64 -M virt -cpu cortex-a72 -m 128M -nographic -no-reboot -semihosting -kernel "$out/kernel.elf"
