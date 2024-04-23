use model::block;

pub struct BlockMock;

impl BlockMock {
    pub fn spawn() {
        /// I will need several things :
        /// 1. I will need a way to read throught input file (either before spawning the thread or after)
        /// 2. Knowing when a block should be spawn (communication with a bed thread ? or maybe using only one thread to manage everything)
        /// 3. Interface with the current implementation (hash, format, transactions tracking)
        /// 
        /// Performance whise, it seams easier to go with the idea of loading and parsing the file before running the tests
        /// Also the idea of a bed thread seams a lot easier to manage than a thread network, need to think hard about this one casue then I would mock
        /// everything at once
        /// 
        /// Finally, it might be a good idea to just start working uh, but it's so boooooooring
        /// I think I will just write on my side project, it seams better
        /// 
        /// Just thought of something, what is actually possible is to setup beforehead the channels, because we always
        /// want a block to be added when 
        /// 
        /// Hhmmmm no my bad we need to schedule them correctly ... because I might want to delay the vertex output
        /// 
        /// 
        /// AHAHAHAHAH and I still have to check on the internal state of the system cause if I don't do it I'm gonna 
        /// be crushed by my supervisors, hhmmmmmmmmmmmmmmmmmmmmm too bad
        /// And also, funny thing I will just have to check the leader output order and not the rest ^^ at least as a first step
        /// 
        /// And omg the parsing will not be easy, I'll have to project the traces against every single processes
        /// RIP
        /// Hm, in theory I know I could limit myself to the first projection because I know they are equivalent,
        /// that is it does not make any difference to extract all the second projections rather than the first one
        /// because the IOA are undistinguishable
        /// 
        /// I will have to be careful then with the scheduler because I'll have to run it at the same time as the process tested
        /// We'll see on the data pre-processing later, right now I'll just build up the mock and test it
    }
}


pub async fn