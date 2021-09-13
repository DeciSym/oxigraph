#!/usr/bin/env bash

DATASET_SIZE=10000 # number of products in the dataset. There is around 350 triples generated by product.
PARALLELISM=5
cd bsbm-tools
./generate -fc -pc ${DATASET_SIZE} -s nt -fn "explore-${DATASET_SIZE}" -ud -ufn "explore-update-${DATASET_SIZE}"
cargo build --release --manifest-path="../../server/Cargo.toml"
./../../target/release/oxigraph_server --file oxigraph_data --bind 127.0.0.1:7878 &
sleep 5
curl -f -X POST -H 'Content-Type:application/n-triples' --data-binary "@explore-${DATASET_SIZE}.nt" http://127.0.0.1:7878/store?default
./testdriver -mt ${PARALLELISM} -ucf usecases/explore/sparql.txt -o "../bsbm.explore.oxigraph.${DATASET_SIZE}.${PARALLELISM}.main.xml" http://127.0.0.1:7878/query
./testdriver -mt ${PARALLELISM} -ucf usecases/exploreAndUpdate/sparql.txt -o "../bsbm.exploreAndUpdate.oxigraph.${DATASET_SIZE}.${PARALLELISM}.main.xml" http://127.0.0.1:7878/query -u http://127.0.0.1:7878/update -udataset "explore-update-${DATASET_SIZE}.nt"
#./testdriver -mt ${PARALLELISM} -ucf usecases/businessIntelligence/sparql.txt -o "../bsbm.businessIntelligence.${DATASET_SIZE}.${PARALLELISM}.main.xml" "http://127.0.0.1:7878/query"
kill $!
rm -r oxigraph_data
rm "explore-${DATASET_SIZE}.nt"
rm -r td_data