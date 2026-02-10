.PHONY: clean all

all: src/rw src/abort/abort.bin

src/rw: src/extraction/Picinae_armv7_lifter.ml src/extraction/arm7_cfi.ml src/main.ml
	cd src; \
	find -name '*.mli' -delete; \
	ocamlfind ocamlopt \
		-package domainslib \
		-linkpkg \
		-nodynlink \
		-ccopt -lm \
		-ccopt -static \
		-ccopt -lpthread \
		-I extraction \
		extraction/Picinae_armv7_lifter.ml extraction/arm7_cfi.ml main.ml \
		-o rw

src/abort/abort.bin: src/abort/abort.elf
	armv7l-unknown-linux-gnueabihf-objcopy -O binary -j .text $< $@
src/abort/abort.elf: src/abort/abort.o src/abort/link.ld
	armv7l-unknown-linux-gnueabihf-ld -T $(word 2,$^) -nostdlib $< -o $@
src/abort/abort.o: src/abort/abort.c
	armv7l-unknown-linux-gnueabihf-gcc -c -O2 -ffreestanding -fno-stack-protector $< -o $@

clean:
	-cd src; \
	find extraction -type f ! \( -name "Picinae_armv7_lifter.ml" -o -name "arm7_cfi.ml" \) -delete; \
	rm rw *.cmi *.cmx *.o
	-rm -r cfitmp
	-rm src/abort/*.{o,bin,elf}
