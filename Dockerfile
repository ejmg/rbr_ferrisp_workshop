FROM rust:1.44 as build

WORKDIR /usr/app

COPY ./ ./

RUN cargo build --release

RUN cargo install --path . --verbose

# RUN cp target/release/rami /out/

CMD ["ferrisp"]
