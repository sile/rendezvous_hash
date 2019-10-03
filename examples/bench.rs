extern crate clap;
extern crate rendezvous_hash;

use clap::{App, Arg};
use rendezvous_hash::RendezvousNodes;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::iter::FromIterator;
use std::time::Instant;

fn main() {
    let matches = App::new("bench")
        .arg(Arg::with_name("WORD_FILE").index(1).required(true))
        .arg(
            Arg::with_name("NODES")
                .long("nodes")
                .required(true)
                .takes_value(true)
                .min_values(1)
                .multiple(true),
        )
        .get_matches();

    let filepath = matches.value_of("WORD_FILE").unwrap();
    let words: Vec<_> = BufReader::new(File::open(filepath).expect("Cannot open file"))
        .lines()
        .collect::<Result<_, _>>()
        .expect("Cannot read words");
    println!("WORD COUNT: {}", words.len());

    let mut nodes = RendezvousNodes::default();
    nodes.extend(matches.values_of("NODES").unwrap());
    println!("NODE COUNT: {}", nodes.len());

    let start_time = Instant::now();
    for word in words.iter() {
        nodes.calc_candidates(word).nth(0).unwrap();
    }
    let end_time = Instant::now();

    let mut counts: HashMap<&str, _> = HashMap::from_iter(nodes.iter().map(|k| (*k, 0)));
    for word in words.iter() {
        let selected = nodes.calc_candidates(word).nth(0).unwrap();
        *counts.get_mut(selected).unwrap() += 1;
    }

    println!("");
    println!("SELECTED COUNT PER NODE:");
    for (node, count) in counts {
        println!("- {}: \t{}", node, count);
    }
    println!("");

    let elapsed = end_time - start_time;
    let elapsed_micros = elapsed.as_secs() * 1_000_000 + (elapsed.subsec_nanos() / 1000) as u64;
    println!("ELAPSED: {} ms", elapsed_micros / 1000);
    println!(
        "WORDS PER SECOND: {}",
        (((words.len() as f64) / (elapsed_micros as f64)) * 1_000_000.0) as u64
    );
}
