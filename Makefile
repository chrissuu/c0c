c0c: bin
	lake build c0c
	cp .lake/build/bin/c0c bin/c0c
	chmod +x bin/c0c

bin:
	mkdir -p bin

clean:
	rm -rf bin
	lake clean

nocache:
	lake build --no-cache c0c
	cp .lake/build/bin/c0c bin/c0c
	chmod +x bin/c0c
