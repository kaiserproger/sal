FROM rust:1.90-bookworm AS builder
WORKDIR /build
COPY Cargo.toml Cargo.lock ./
COPY crates ./crates
COPY stdlib ./stdlib
COPY apps/warehouse ./apps/warehouse
RUN cargo build --release --locked -j 2 -p sal_cli \
    && target/release/sal build-exe apps/warehouse/main.sal --out /out/app --strict \
    && target/release/sal build-exe apps/warehouse/healthcheck.sal --out /out/probe --strict

FROM scratch
COPY --from=builder /out/app/main /warehouse
COPY --from=builder /out/probe/healthcheck /healthcheck
USER 65532:65532
EXPOSE 8080
ENTRYPOINT ["/warehouse"]
