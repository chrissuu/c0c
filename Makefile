c0vc: bin
	lake build c0vc
	cp .lake/build/bin/c0vc bin/c0vc
	chmod +x bin/c0vc

bin:
	mkdir -p bin

clean:
	rm -rf bin
	lake clean

nocache:
	lake build --no-cache c0vc
	cp .lake/build/bin/c0vc bin/c0vc
	chmod +x bin/c0vc
