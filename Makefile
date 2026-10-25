.PHONY: build up stop test integration-test logs

build:
	cargo build --release --locked -j 2 -p sal_cli
	target/release/sal build-exe apps/warehouse/main.sal --out build/warehouse --strict
	target/release/sal build-exe apps/warehouse/healthcheck.sal --out build/healthcheck --strict

up:
	docker compose up --build -d --wait --wait-timeout 180

stop:
	docker compose stop

test:
	cargo test --workspace --locked -j 2

integration-test: up
	cargo build --release --locked -j 2 -p sal_cli
	SAL_TEST_POSTGRES_SOCKET="$(CURDIR)/.warehouse-state/socket/.s.PGSQL.5432" \
	SAL_TEST_POSTGRES_CONTAINER="$$(docker compose ps -q db)" \
	SAL_COMPILER="$(CURDIR)/target/release/sal" \
	python3 apps/warehouse/test_api.py

logs:
	docker compose logs --tail 100 app db
