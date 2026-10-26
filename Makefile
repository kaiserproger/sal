.PHONY: compiler build up stop test stdlib-test solaris-test integration-test logs

compiler:
	cargo build --release --locked -j 2 -p sal_cli

build: compiler
	target/release/sal build-exe apps/warehouse/main.sal --out build/warehouse --strict
	target/release/sal build-exe apps/warehouse/healthcheck.sal --out build/healthcheck --strict

up:
	docker compose up --build -d --wait --wait-timeout 180

stop:
	docker compose stop

test:
	cargo test --workspace --locked -j 2
	$(MAKE) stdlib-test
	$(MAKE) solaris-test

stdlib-test: SAL_TEST_SOURCES = $(wildcard crates/sal_cli/tests/fixtures/stdlib/*.sal)
solaris-test: SAL_TEST_SOURCES = examples/solaris/protocol.sal examples/solaris/index_store.sal examples/solaris/snapshot_merge.sal

stdlib-test solaris-test: compiler
	@set -eu; \
	work=$$(mktemp -d); \
	trap 'rm -rf -- "$$work"' EXIT; \
	set -- $(SAL_TEST_SOURCES); \
	test "$$#" -gt 0; \
	for source do \
		name=$${source##*/}; name=$${name%.sal}; \
		target/release/sal build-exe "$$source" --out "$$work/$$name" --strict; \
		(cd "$$work" && timeout 30 "$$work/$$name/$$name"); \
	done

integration-test:
	@set -eu; \
	project="sal-warehouse-qa-$$(date +%s)-$$$$"; \
	export WAREHOUSE_PORT=0; \
	trap 'code=$$?; trap - EXIT; if ! docker compose -p "$$project" --profile qa down --volumes --remove-orphans; then test "$$code" -ne 0 || code=1; fi; exit "$$code"' EXIT; \
	docker compose -p "$$project" up --build -d --wait --wait-timeout 180 app db; \
	docker compose -p "$$project" --profile qa run --build --rm --no-deps qa

logs:
	docker compose logs --tail 100 app db
