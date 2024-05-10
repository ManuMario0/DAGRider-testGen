use std::collections::HashMap;
use model::{block::Block, committee::Committee, vertex::Vertex};
use std::collections::BTreeMap;
use super::parser;
use tokio::sync::mpsc::{Receiver, Sender};
use tokio;

pub struct Environment {
    block_channel_propose: Sender<Block>,
    vertex_channel_broadcast: Receiver<Vertex>,
    vertex_channel_deliver: Sender<Vertex>,
    process_id : u8,
    run : parser::Run,
    states : std::sync::Arc<HashMap<i64, parser::TlaState>>,
    control_sender : Sender<parser::TlaState>
}

impl Environment {
    pub fn spawn(
        block_channel_propose: Sender<Block>,
        vertex_channel_broadcast: Receiver<Vertex>,
        vertex_channel_deliver: Sender<Vertex>,
        run : parser::Run,
        states : std::sync::Arc<HashMap<i64, parser::TlaState>>,
        process_id : u8,
        control_sender : Sender<parser::TlaState>
    ) {
        tokio::spawn(async move {
            Self {
                block_channel_propose,
                vertex_channel_broadcast,
                vertex_channel_deliver,
                process_id,
                run,
                states,
                control_sender
            }
            .run()
            .await;
        });
    }

    async fn run(&mut self) {
        let mut current_state  : parser::TlaState = self.states.get(&self.run.start).unwrap().clone();
        for (act, id_next_action) in self.run.clone().actions.iter() {
            let next_state : parser::TlaState = self.states.get(&id_next_action).unwrap().clone();
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
        let vertex = Environment::generate_vertex(next_state, process_source, next_state.process_state[process_dest][process_source] as usize);

        // print!("I added a vertex {} ; ", &vertex);

        // send the vertex
        self.vertex_channel_deliver.send(vertex).await.unwrap();

        self.control_sender.send(current_state.clone()).await.unwrap();
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
    async fn process_next_round_action(&mut self, current_state : &parser::TlaState, action : &parser::Action, next_state : &parser::TlaState) {
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
        let block: Block = Environment::generate_block(next_state.dag[process_source][next_state.process_state[process_dest][process_source] as usize].block);

        // print!("I went to next round {:?} ; ", block);

        // propose block
        self.block_channel_propose.send(block).await.unwrap();

        self.control_sender.send(current_state.clone()).await.unwrap();

        // TODO: check tmp here !!!!!!!!
        let tmp = self.vertex_channel_broadcast.recv().await.unwrap();

        for v in current_state.dag[process_source][next_state.process_state[process_dest][process_source] as usize].strongedges.iter() {
            let vert = Environment::generate_vertex(current_state, v.source as usize-1, v.round as usize);
            if !tmp.get_strong_parents().contains_key(&vert.hash()) {
                println!("ERROR !");
            }
        }

        for v in current_state.dag[process_source][next_state.process_state[process_dest][process_source] as usize].weakedges.iter() {
            let vert = Environment::generate_vertex(current_state, v.source as usize-1, v.round as usize);
            if tmp.get_strong_parents().contains_key(&vert.hash()) || !tmp.get_all_parents().contains_key(&vert.hash()) {
                println!("ERROR !");
            }
        }

        let vertex = Environment::generate_vertex(next_state, process_source, next_state.process_state[process_dest][process_source] as usize);

        self.vertex_channel_deliver.send(vertex).await.unwrap();

        // check output
        self.control_sender.send(current_state.clone()).await.unwrap();
    }

    fn generate_block(id : u64) -> Block {
        Block::new(vec![vec![id as u8]])
    }

    pub fn generate_vertex(current_state : &parser::TlaState, process_source : usize, round : usize) -> Vertex {
        // if round zero send genesis vertex hash
        if round == 0 {
            return Vertex::new(Committee::default().get_node_key(process_source as u32 + 1).unwrap(), 1, Block::default(), BTreeMap::new());
        }

        // else we compute the hash recursively
        // get parents
        let mut parents : BTreeMap<[u8; 32], u64> = BTreeMap::new();
        for v in current_state.dag[process_source][round].strongedges.iter() {
            let vert = Environment::generate_vertex(current_state, v.source as usize-1, v.round as usize);
            parents.insert(vert.hash(), v.round+1);
        }

        for v in current_state.dag[process_source][round].weakedges.iter() {
            let vert = Environment::generate_vertex(current_state, v.source as usize-1, v.round as usize);
            parents.insert(vert.hash(), v.round+1);
        }

        // let keys = Committee::default().get_nodes_keys();

        Vertex::new(Committee::default().get_node_key(process_source as u32+1).unwrap(), round as u64+1, Environment::generate_block(current_state.dag[process_source][round].block), parents)
    }
}

#[test]
fn test_generate_vertex() {
    let current_test = parser::TlaState {process_state : vec![], dag : vec![]};
    let _ = Environment::generate_vertex(&current_test, 3, 0);
}