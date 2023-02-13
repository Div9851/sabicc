SRCS=$(wildcard *.rs)

TEST_SRCS=$(wildcard test/*.c)
TESTS=$(TEST_SRCS:.c=.out)

test/%.out: Cargo.toml $(SRCS) test/%.c
	$(CC) -o- -E -P -C test/$*.c | cargo run -- -o test/$*.s -
	$(CC) -o $@ test/$*.s -xc test/common

test: $(TESTS)
	for i in $^; do echo $$i; ./$$i || exit 1; echo; done
	test/driver.sh

clean:
	rm -rf tmp* $(TESTS) test/$*.s test/$*.out
	find * -type f '(' -name  '*~' -o -name '*.o' ')' -exec rm {} ';'

.PHONY: test clean
