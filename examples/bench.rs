extern crate clap;
extern crate rendezvous_hash;

use std::collections::HashMap;
use std::io::{BufRead, BufReader};
use std::fs::File;
use std::iter::FromIterator;
use clap::{App, Arg};
use rendezvous_hash::RendezvousNodes;

fn main() {
    let matches = App::new("bench")
        .arg(Arg::with_name("WORD_FILE")
            .index(1)
            .required(true))
        .arg(Arg::with_name("NODES")
            .long("nodes")
            .required(true)
            .takes_value(true)
            .min_values(1)
            .multiple(true))
        .get_matches();
    let filepath = matches.value_of("WORD_FILE").unwrap();
    let mut nodes = RendezvousNodes::default();
    nodes.extend(matches.values_of("NODES").unwrap());

    let mut selected_counts: HashMap<&str, _> =
        HashMap::from_iter(matches.values_of("NODES").unwrap().map(|k| (k, 0)));
    for line in BufReader::new(File::open(filepath).expect("Cannot open file")).lines() {
        let line = line.expect("Cannot read a line");
        let selected = nodes.calc_candidates(&line).nth(0).unwrap();
        *selected_counts.get_mut(selected).unwrap() += 1;
    }

    println!("SELECTED COUNT: {:?}", selected_counts);
}
