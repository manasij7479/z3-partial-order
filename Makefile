all : release

.PHONY :  debug release clean patch test

debug : z3/buildd/libz3.so
release : z3/buildr/libz3.so

z3/buildd/libz3.so : z3/patched z3/buildd/rules.ninja $(wildcard new_files/*)
	ninja -C z3/buildd
	# make -C z3/buildd -j9
	ln -sf z3/buildd/z3 z3.out

z3/buildr/libz3.so : z3/patched z3/buildr/rules.ninja $(wildcard new_files/*)
	ninja -C z3/buildr
	# make -C z3/buildd -j9
	ln -sf z3/buildr/z3 z3.out.release #change

z3/buildd/rules.ninja: utils/link_extra_files.sh
	cd utils; ./link_extra_files.sh;
	mkdir -p z3/buildd
	# cd z3; python scripts/mk_make.py --staticlib -d -t -b buildd
	cd z3/buildd; cmake -DCMAKE_BUILD_TYPE=Debug ../ -GNinja

z3/buildr/rules.ninja: utils/link_extra_files.sh
	cd utils; ./link_extra_files.sh;
	mkdir -p z3/buildr
	# cd z3; python scripts/mk_make.py --staticlib -d -t -b buildd
	cd z3/buildr; cmake -DCMAKE_BUILD_TYPE=Release ../ -GNinja

z3/patched : po.patch z3/README.md
	cd z3; git stash clear && git stash save && git apply --whitespace=fix $(PWD)/po.patch
	touch z3/patched

z3/README.md :
	rm -rf z3
	git clone https://github.com/Z3Prover/z3
	cd z3; git reset --hard d3320f8b8143c64badc1a291fd210bb4aef96693
	git init z3
	cd z3;git add -A; git diff-index --quiet HEAD || git commit -m "clean z3 version"

clean :
	rm -rf $(PWD)/z3/buildd
	rm -rf $(PWD)/z3/buildr

patch :
	cd z3; git diff > ../po.patch

test : debug
	cd utils; rm -rf tests outs; ./test-ref.sh
