use dict::{Dict, DictIface};
use model::{block::Block, committee::Committee, vertex::Vertex, DEFAULT_CHANNEL_CAPACITY};
use std::fs::File;
use std::io::Read;
use std::collections::BTreeMap;
use crate::parser;
use tokio::sync::mpsc::{channel, Receiver, Sender};
use tokio;
use std::io::Write;
use std::io::stdout;

use transaction::TransactionCoordinator;
use vertex::vertex_coordinator::VertexCoordinator;
use consensus::Consensus;

pub struct Environment {
    block_channel_propose: Sender<Block>,
    vertex_channel_broadcast: Receiver<Vertex>,
    vertex_channel_deliver: Sender<Vertex>,
    process_id : u8,
    run : parser::Run,
    states : Dict<parser::TlaState>
}

impl Environment {
    pub fn spawn(
        block_channel_propose: Sender<Block>,
        vertex_channel_broadcast: Receiver<Vertex>,
        vertex_channel_deliver: Sender<Vertex>,
        run : parser::Run,
        states : Dict<parser::TlaState>,
        process_id : u8
    )  -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            Self {
                block_channel_propose,
                vertex_channel_broadcast,
                vertex_channel_deliver,
                process_id,
                run,
                states
            }
            .run()
            .await;
        })
    }

    async fn run(&mut self) {
        let mut current_state  : parser::TlaState = self.states.get(&self.run.start.to_string()).unwrap().clone();
        for (act, id_next_action) in self.run.actions.iter() {
            let next_state : parser::TlaState = self.states.get(&id_next_action.to_string()).unwrap().clone();
            match *act {
                | parser::Action::AddVertex => 
                    {
                        self.process_add_vertex_action(&current_state, act, &next_state).await;
                        current_state = next_state;
                    }
                ,
                | parser::Action::NextRound => 
                    {
                        self.process_next_round_action(&current_state, act, &next_state).await;
                        current_state = next_state;
                    }
            }
        }
    }

    /*
    When we add a vertex to the dag of one of the process, we have to do several things :
    - we have to check if the vertex was added to the process we were working on (if not, we just ignore it)
    - we have to create the corresponding block for the next step
    - we have to then create the corresponding vertex in the implementation
    - we finally have to send it to the process via the vertex_channel_broadcast
    */
    async fn process_add_vertex_action(&self, current_state : &parser::TlaState, action : &parser::Action, next_state : &parser::TlaState) {
        // check which vertex has been added by running trough the process_state
        let mut process_source = 0;
        let mut process_dest = 0;
        'check_change: for (i, v) in current_state.process_state.iter().enumerate() {
            for (j, e) in v.iter().enumerate() {
                if *e != next_state.process_state[i][j] {
                    process_dest = i;
                    process_source = j;
                    break 'check_change;
                }
            }
        }

        if process_dest != self.process_id.into() {
            return;
        }

        // now create the vertex that has to be added (this is the extremly tricky bit)
        let vertex = Environment::generate_vertex(current_state, process_source, next_state.process_state[process_dest][process_source] as usize);

        // send the vertex
        self.vertex_channel_deliver.send(vertex).await.unwrap();

        print!("I added a vertex ; ");
    }

    /*
    For the next round, we have to do some more work because we have to check the output of the program too here :
    - we have to check if the process that triggered the action is the one we're working on
    - we have then to create the corresponding block
    - we send this block to the process vie block_channel_propose
    - we wait for an answer on vertex_channel_deliver (with timeout, if no vertex is ever delivered, that means there has been an internal error)
    - we check that the vertex received is the one we expected by reconstrcuting it by ourselfs against the model
    - finally, check for block_channel_deliver to check if the blocks are delivered in the correct order
        (this part is not really possible right now, what is possible is to check if the leaders are proposed in the correct order,
            which is enough if the ordering algorithm is deterministic and the same for all process, which it is)
    */
    async fn process_next_round_action(&self, current_state : &parser::TlaState, action : &parser::Action, next_state : &parser::TlaState) {
        // check which vertex has been added by running trough the process_state
        let mut process_source = 0;
        let mut process_dest = 0;
        'check_change: for (i, v) in current_state.process_state.iter().enumerate() {
            for (j, e) in v.iter().enumerate() {
                if *e != next_state.process_state[i][j] {
                    process_dest = i;
                    process_source = j;
                    break 'check_change;
                }
            }
        }

        if process_source != self.process_id.into() {
            return;
        }

        // create block
        let block = Environment::generate_block(next_state.dag[process_source][next_state.process_state[process_dest][process_source] as usize].block);

        // propose block
        self.block_channel_propose.send(block).await.unwrap();

        // check output
        print!("I went to next round ; ");
    }

    fn generate_block(id : u64) -> Block {
        Block::new(vec![vec![id as u8]])
    }

    fn generate_vertex(current_state : &parser::TlaState, process_source : usize, round : usize) -> Vertex {
        // if round zero send genesis vertex hash
        if round == 0 {
            let genesis = Vertex::genesis(Committee::default().get_nodes_keys());

            return genesis.get(process_source-1).unwrap().clone()
        }

        // else we compute the hash recursively
        // get parents
        let mut parents : BTreeMap<[u8; 32], u64> = BTreeMap::new();
        for v in current_state.dag[process_source][round].strongedges.iter() {
            let vert = Environment::generate_vertex(current_state, v.source as usize, v.round as usize);
            parents.insert(vert.hash(), v.round);
        }

        for v in current_state.dag[process_source][round].weakedges.iter() {
            let vert = Environment::generate_vertex(current_state, v.source as usize, v.round as usize);
            parents.insert(vert.hash(), v.round);
        }

        let keys = Committee::default().get_nodes_keys();

        Vertex::new(keys[process_source], round as u64, Environment::generate_block(current_state.dag[process_source][round].block), parents)
    }
}

#[test]
fn test_generate_vertex() {
    let current_test = parser::TlaState {process_state : vec![], dag : vec![]};
    let _ = Environment::generate_vertex(&current_test, 3, 0);
}



#[cfg(test)]
#[tokio::test]
async fn test_environment_creation() {
    let mut file = File::open("ressources/state.edge").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();
    let edge_parse = parser::edge_parser::file(&contents).unwrap();

    file = File::open("ressources/state.node").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();

    for v in edge_parse.iter() {
        let node_id = 0;

        let node_parse = parser::node_parser::file(&contents).unwrap();

        let (vertex_output_sender, vertex_output_receiver) =
        channel::<Vertex>(DEFAULT_CHANNEL_CAPACITY);

        let (vertex_to_broadcast_sender, vertex_to_broadcast_receiver) =
            channel::<Vertex>(DEFAULT_CHANNEL_CAPACITY);
        let (vertex_to_consensus_sender, vertex_to_consensus_receiver) =
            channel::<Vertex>(DEFAULT_CHANNEL_CAPACITY);
        let (block_sender, block_receiver) = channel::<Block>(DEFAULT_CHANNEL_CAPACITY);

        Consensus::spawn(
            node_id+1,
            Committee::default(),
            vertex_to_consensus_receiver,
            vertex_to_broadcast_sender,
            vertex_output_sender,
            block_receiver,
        );

        let _ = tokio::join!(Environment::spawn(
            block_sender, 
            vertex_to_broadcast_receiver, 
            vertex_to_consensus_sender,
            v.clone(),
            node_parse,
            node_id as u8
        ));

        println!("Test done !");
    }
}