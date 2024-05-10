mod environment;
mod parser;

use environment::Environment;

use indicatif::MultiProgress;
use model::{block::Block, committee::Committee, vertex::Vertex, DEFAULT_CHANNEL_CAPACITY};
use parser::TlaState;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::time::Duration;
use tokio::sync::mpsc::channel;
use tokio;
use consensus::Consensus;
use consensus::dag;
use indicatif::ProgressBar;

async fn run_test(
    node_id : u32,
    bar : ProgressBar,
    node_parse_ref : std::sync::Arc<HashMap<i64, TlaState>>,
    edge_parse : std::sync::Arc<Vec<parser::Run>>,
) {
    'main_loop: for v in edge_parse.iter() {
        bar.inc(1);

        let (vertex_output_sender, vertex_output_receiver) =
        channel::<Vertex>(DEFAULT_CHANNEL_CAPACITY);

        let (vertex_to_broadcast_sender, vertex_to_broadcast_receiver) =
            channel::<Vertex>(DEFAULT_CHANNEL_CAPACITY);
        let (vertex_to_consensus_sender, vertex_to_consensus_receiver) =
            channel::<Vertex>(DEFAULT_CHANNEL_CAPACITY);
        let (block_sender, block_receiver) = channel::<Block>(DEFAULT_CHANNEL_CAPACITY);

        let (control_sender, mut control_receiver) =
            channel::<parser::TlaState>(DEFAULT_CHANNEL_CAPACITY);
        let (test_sender, mut test_receiver) =
            channel::<dag::Dag>(DEFAULT_CHANNEL_CAPACITY);

        Consensus::spawn(
            node_id,
            Committee::default(),
            vertex_to_consensus_receiver,
            vertex_to_broadcast_sender,
            vertex_output_sender,
            block_receiver,
            test_sender
        );

        Environment::spawn(
            block_sender,
            vertex_to_broadcast_receiver,
            vertex_to_consensus_sender,
            v.clone(),
            node_parse_ref.clone(),
            node_id as u8-1,
            control_sender
        );

        'check_states: loop {
            match control_receiver.recv().await {
                Some(state) => 
                match test_receiver.recv().await {
                    Some(dag) => {
                        let round = state.process_state[node_id as usize-1][node_id as usize-1] + 1;
                        /*let vertex = dag.get_vertices(round) dag.get_vertex(Committee::default().get_node_key(node_id).unwrap(), &round).unwrap();*/
                        let control_vertex = Environment::generate_vertex(&state, node_id as usize-1, state.process_state[node_id as usize-1][node_id as usize-1] as usize);
                        /*let control_vertex = &state.dag[node_id as usize-1][state.process_state[node_id as usize-1][node_id as usize-1] as usize];*/

                        /*assert_eq!(vertex.hash(), control_vertex.hash())*/
                        match dag.get_vertex(control_vertex.hash(), &round) {
                            Some(_) => (),
                            None => {
                                println!("Dag inconsistent !");
                                break 'main_loop
                            }
                        }
                    },
                    None => {
                        println!("Dag inconsistent !");
                        break 'main_loop;
                    }
                }
                ,
                None => break 'check_states,
            }
        }
    }
    bar.finish_with_message(format!("[ Running tests for process {node_id} ]"));
}

#[tokio::main]
async fn main() {
    let mut spinner = ProgressBar::new_spinner();
    spinner.enable_steady_tick(Duration::from_millis(100));
    spinner.set_message("[ Parsing edges ]");

    let mut file = File::open("ressources/state.edge").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();
    let edge_parse = parser::edge_parser::file(&contents).unwrap();
    let edge_parse_ref = std::sync::Arc::new(edge_parse);

    spinner.finish_with_message("[ Parsing edges ] Done");

    spinner = ProgressBar::new_spinner();
    spinner.enable_steady_tick(Duration::from_millis(100));
    spinner.set_message("[ Parsing nodes ]");

    file = File::open("ressources/state.node").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();

    let node_parse = parser::node_parser::file(&contents).unwrap();
    let node_parse_ref = std::sync::Arc::new(node_parse);

    spinner.finish_with_message("[ Parsing nodes ] Done");

    let mut handle = vec![];

    let multibar = MultiProgress::new();
    for i in 1..5 {
        let bar = ProgressBar::new(edge_parse_ref.len() as u64);
        let bar_finish = multibar.add(bar);
        bar_finish.set_message(format!("[ Running tests for process {i} ]"));
        bar_finish.set_style(indicatif::ProgressStyle::with_template("  {msg} {bar:60.cyan/blue} {pos:>7}/{len:7} [{elapsed_precise}]")
            .unwrap()
            .progress_chars("#+-"));
        let i_r = i.clone();
        let node_parse_ref_r = node_parse_ref.clone();
        let edge_parse_ref_r = edge_parse_ref.clone();
        handle.push(tokio::spawn(async move {
            run_test(i_r, bar_finish, node_parse_ref_r, edge_parse_ref_r).await;
        }));
    }
    for v in handle {
        let _ = v.await;
    }
}