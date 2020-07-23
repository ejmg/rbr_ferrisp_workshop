FROM rust:1.44 as build

WORKDIR /usr/app

COPY ./ ./

RUN cargo build --release

RUN cargo install --path .

FROM debian:stable-slim as final 

COPY --from=build /usr/local/cargo/bin/ferrisp /bin

# run with logging passed in:
# docker run --env RUST_LOG=info -it --rm --name ferrisp ferrisp
CMD ["ferrisp"]
