use dict::{ Dict, DictIface };
use std::fs::File;
use std::io::prelude::*;

use peg;

#[derive(Debug, PartialEq, Clone)]
pub struct TlaLighVertex {
    pub round: u64,
    pub source: u64,
}

#[derive(Debug, PartialEq, Clone)]
pub struct TlaFullVertex {
    pub block: u64,
    pub strongedges: Vec<TlaLighVertex>,
    pub weakedges: Vec<TlaLighVertex>,
}

pub type TlaDag = Vec<Vec<TlaFullVertex>>;
pub type TlaProcessState = Vec<Vec<u64>>;

#[derive(Debug, PartialEq, Clone)]
pub struct TlaState {
    pub process_state: TlaProcessState,
    pub dag: TlaDag,
}

peg::parser! {
    pub grammar node_parser() for str {
        rule whitespace() = quiet!{([' ' | '\n' | '\t'] / "\\n")*}

        rule integer() -> u64
            = whitespace() n:$(['0'..='9']+) whitespace() {? n.parse().or(Err("u64"))}

        rule signed_integer() -> i64
            = whitespace() signed:("-"?) n:(integer()) whitespace() {
                match signed {
                    Some(_) => -(n as i64),
                    None => n as i64
                }
             }

        rule int_seq() -> Vec<u64>
            = whitespace() "<<" l:(integer() ** ",") ">>" whitespace() { l }

        rule int_seq_seq() -> Vec<Vec<u64>>
            = whitespace() "<<" l:(int_seq() ** ",") ">>" whitespace() { l }

        pub rule light_vertex() -> TlaLighVertex
            = whitespace() "["
                whitespace() "round"
                whitespace() "|->"
                whitespace() r:(integer())
                whitespace() ","
                whitespace() "source"
                whitespace() "|->"
                whitespace() s:(integer())
                whitespace() "]"
                whitespace() { TlaLighVertex { round: r, source: s } }

        rule light_vertex_set() -> Vec<TlaLighVertex>
            = whitespace() "{" l:(light_vertex() ** ",") "}" whitespace() { l }

        pub rule full_vertex() -> TlaFullVertex
            = whitespace() "["
                whitespace() "block"
                whitespace() "|->"
                whitespace() b:(integer())
                whitespace() ","
                whitespace() "strongedges"
                whitespace() "|->"
                whitespace() se:(light_vertex_set())
                whitespace() ","
                whitespace() "weakedges"
                whitespace() "|->"
                whitespace() we:(light_vertex_set())
                [^']']* "]"
                { TlaFullVertex { block : b, strongedges : se, weakedges : we} }

        rule dag_row_line() -> TlaFullVertex
             = whitespace() integer()
                whitespace() ":>"
                whitespace() v:(full_vertex())
                whitespace() { v }


        pub rule dag_row() -> Vec<TlaFullVertex>
            = whitespace() "("
                whitespace() l:(dag_row_line() ** ("@@"))
                whitespace() ")" whitespace() { l }

        pub rule dag() -> TlaDag
            = whitespace() "<<"
                whitespace() l:(dag_row() ** ",")
                whitespace() ">>"
                whitespace() { l }

        pub rule process_state() -> TlaProcessState
            = l:(int_seq_seq()) { l }

        pub rule state() -> (i64, TlaState)
            = whitespace() id:(signed_integer()) [^ 'P']*
            "ProcessState" whitespace() "=" process_state:(process_state()) [^ 'd']*
            "dag" whitespace() "=" dag:(dag()) [^'\n']*
            { (id, TlaState {process_state, dag}) }
        
        pub rule file() -> Dict::<TlaState>
             = l:(state() ** "\n") whitespace() {
                let mut d = Dict::<TlaState>::new();
                for x in &l {
                    d.add( (x.0).to_string(), x.1.clone());
                }
                d
             }
    }
}

#[test]
fn parser_light_vertex() {
    assert_eq!(
        node_parser::light_vertex("[ round |-> 5, source |-> 538 ]"),
        Ok(TlaLighVertex {
            round: 5,
            source: 538
        })
    )
}

#[test]
fn parser_full_vertex_empty() {
    assert_eq!(node_parser::full_vertex(
        "[ block |-> 1\n\t , strongedges |-> {} \t, weakedges |-> {} , reachableleaders |-> {} ]"
    ), Ok(TlaFullVertex {block : 1, strongedges : vec![], weakedges : vec![]} ))
}

#[test]
fn parser_full_vertex_full() {
    assert_eq!(node_parser::full_vertex(
        "[ block |-> 62 , strongedges |-> {[round |-> 3, source |-> 1], [round |-> 12, source |-> 932]} \t,
            weakedges |-> {[round |-> 13, source |-> 72], [round |-> 274, source |-> 321]} , reachableleaders |-> {2, 65, 0} ]"
    ), Ok(TlaFullVertex {
        block : 62,
        strongedges : vec![
            TlaLighVertex {round : 3, source : 1},
            TlaLighVertex {round : 12, source : 932}
        ],
        weakedges : vec![
            TlaLighVertex {round : 13, source : 72},
            TlaLighVertex {round : 274, source : 321}
        ]
    }))
}

#[test]
fn parser_dag() {
    assert_eq!(
        node_parser::dag("
            << (0 :> [ block |-> 62 , strongedges |-> {[round |-> 3, source |-> 1], [round |-> 12, source |-> 932]} \t,
                weakedges |-> {[round |-> 13, source |-> 72], [round |-> 274, source |-> 321]} , reachableleaders |-> {2, 65, 0} ] @@
                1 :> [ block |-> 62 , strongedges |-> {[round |-> 3, source |-> 1], [round |-> 12, source |-> 932]} \t,
                weakedges |-> {[round |-> 13, source |-> 72], [round |-> 274, source |-> 321]} , reachableleaders |-> {2, 65, 0} ]
            ),
            (0 :> [ block |-> 62 , strongedges |-> {[round |-> 3, source |-> 1], [round |-> 12, source |-> 932]} \t,
                weakedges |-> {[round |-> 13, source |-> 72], [round |-> 274, source |-> 321]} , reachableleaders |-> {2, 65, 0} ] @@
                1 :> [ block |-> 62 , strongedges |-> {[round |-> 3, source |-> 1], [round |-> 12, source |-> 932]} \t,
                weakedges |-> {[round |-> 13, source |-> 72], [round |-> 274, source |-> 321]} , reachableleaders |-> {2, 65, 0} ]
            )>>
        "),
        Ok(vec![vec![
            TlaFullVertex {
                block : 62,
                strongedges : vec![
                    TlaLighVertex {round : 3, source : 1},
                    TlaLighVertex {round : 12, source : 932}
                ],
                weakedges : vec![
                    TlaLighVertex {round : 13, source : 72},
                    TlaLighVertex {round : 274, source : 321}
                ]
            },TlaFullVertex {
                block : 62,
                strongedges : vec![
                    TlaLighVertex {round : 3, source : 1},
                    TlaLighVertex {round : 12, source : 932}
                ],
                weakedges : vec![
                    TlaLighVertex {round : 13, source : 72},
                    TlaLighVertex {round : 274, source : 321}
                ]
            }
        ], vec![TlaFullVertex {
            block : 62,
            strongedges : vec![
                TlaLighVertex {round : 3, source : 1},
                TlaLighVertex {round : 12, source : 932}
            ],
            weakedges : vec![
                TlaLighVertex {round : 13, source : 72},
                TlaLighVertex {round : 274, source : 321}
            ]
        },TlaFullVertex {
            block : 62,
            strongedges : vec![
                TlaLighVertex {round : 3, source : 1},
                TlaLighVertex {round : 12, source : 932}
            ],
            weakedges : vec![
                TlaLighVertex {round : 13, source : 72},
                TlaLighVertex {round : 274, source : 321}
            ]
        }]])
    )
}

#[test]
fn parser_state() {
    assert_eq!(
        node_parser::state("
            -5216669243417396514 /\\ ProcessState = <<<<1, 0, 0, 0>>, <<0, 0, 0, 0>>, <<0, 0, 1, 0>>, <<0, 0, 0, 0>>>>\\n/\\ dag = << ( 0 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     1 :>\n         [ block |-> 1,\n           strongedges |->\n               { [round |-> 0, source |-> 1],\n                 [round |-> 0, source |-> 2],\n                 [round |-> 0, source |-> 3],\n                 [round |-> 0, source |-> 4] },\n           weakedges |-> {},\n           reachableleaders |-> {1} ] @@\n     2 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     3 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     4 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] ),\n   ( 0 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     1 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     2 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     3 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     4 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] ),\n   ( 0 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     1 :>\n         [ block |-> 2,\n           strongedges |->\n               { [round |-> 0, source |-> 1],\n                 [round |-> 0, source |-> 2],\n                 [round |-> 0, source |-> 3],\n                 [round |-> 0, source |-> 4] },\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     2 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     3 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     4 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] ),\n   ( 0 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     1 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     2 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     3 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] @@\n     4 :>\n         [ block |-> 0,\n           strongedges |-> {},\n           weakedges |-> {},\n           reachableleaders |-> {} ] ) >>\\n/\\ decidedWave = <<0, 0, 0, 0>>\\n/\\ leaderSeq = << [current |-> <<>>, last |-> <<>>],\\n   [current |-> <<>>, last |-> <<>>],\\n   [current |-> <<>>, last |-> <<>>],\\n   [current |-> <<>>, last |-> <<>>] >>\\n/\\ BlockSeq = <<3, 4, 5>>\\n/\\ StrongedgeHead = <<{1}, 1..4, {3}, 1..4>>\\n/\\ commitWithRef = <<<<<<>>>>, <<<<>>>>, <<<<>>>>, <<<<>>>>>>\\n/\\ leaderReachablity = << <<[exists |-> FALSE, edges |-> {}]>>,\\n   <<[exists |-> FALSE, edges |-> {}]>>,\\n   <<[exists |-> FALSE, edges |-> {}]>>,\\n   <<[exists |-> FALSE, edges |-> {}]>> >>"),
        Ok(
            (
                -5216669243417396514,
                TlaState {
                    process_state: vec![vec![1, 0, 0, 0], vec![0, 0, 0, 0], vec![0, 0, 1, 0], vec![0, 0, 0, 0]],
                    dag: vec![
                        vec![TlaFullVertex {
                            block: 0,
                            strongedges: vec![],
                            weakedges: vec![]
                        },
                        TlaFullVertex {
                            block: 1,
                            strongedges: vec![
                                TlaLighVertex { round: 0, source: 1 },
                                TlaLighVertex { round: 0, source: 2 },
                                TlaLighVertex { round: 0, source: 3 },
                                TlaLighVertex { round: 0, source: 4 }
                                ],
                            weakedges: vec![]
                        },
                        TlaFullVertex {
                            block: 0,
                            strongedges: vec![],
                            weakedges: vec![]
                        },
                        TlaFullVertex {
                            block: 0,
                            strongedges: vec![],
                            weakedges: vec![]
                        },
                        TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }], vec![TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }], vec![TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 2, strongedges: vec![TlaLighVertex { round: 0, source: 1 }, TlaLighVertex { round: 0, source: 2 }, TlaLighVertex { round: 0, source: 3 }, TlaLighVertex { round: 0, source: 4 }], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }], vec![TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }, TlaFullVertex { block: 0, strongedges: vec![], weakedges: vec![] }]]
                }
            )
        )
    )
}

#[test]
fn parse_file() -> std::io::Result<()> {
    let mut file = File::open("/Volumes/Emmanuel/state.node")?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    match node_parser::file(&contents) {
        Err(_) => Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "Unable to parse")),
        Ok(m) => {
            //m.iter().for_each( |o| println!( "{} - {:#?}", o.key, o.val ) );
            Ok(())
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Action {
    NextRound,
    AddVertex
}

#[derive(Debug, PartialEq, Clone)]
pub struct Run {
    pub start : i64,
    pub actions: Vec<(Action, i64)>
}

peg::parser!{
    pub grammar edge_parser() for str {
        rule whitespace() = quiet!{([' ' | '\n' | '\t'] / "\\n")*}

        rule integer() -> u64
            = whitespace() n:$(['0'..='9']+) whitespace() {? n.parse().or(Err("u64"))}

        rule signed_integer() -> i64
            = whitespace() signed:("-"?) n:(integer()) whitespace() {
                match signed {
                    Some(_) => -(n as i64),
                    None => n as i64
                }
             }
        
        rule alpha() -> String
             = whitespace() s:$(['a'..='z' | 'A'..='Z']+) whitespace() { s.to_string() }

        rule action() -> Action
             = whitespace() a:alpha() whitespace() {
                if a == "NextRoundTn" {
                    Action::NextRound
                } else {
                    Action::AddVertex
                }
            }

        rule pair() -> (Action, i64)
             = whitespace() a:action() whitespace() i:signed_integer() whitespace() { (a, i) }

        pub rule run() -> Run
             = whitespace() s:signed_integer()
                whitespace() l:(pair() ** whitespace()) [^'\n']* { Run { start : s, actions : l } }

        pub rule file() -> Vec<Run>
            = l:(run() ** "\n") whitespace() { l }
    }
}

#[test]
fn parser_run() {
    assert_eq!(edge_parser::run("8382238128741917860 NextRoundTn 4761280334617038924 NextRoundTn 4307459230874888534 AddVertexTn -1401184906700154449 AddVertexTn -8358486048188273524"),
    Ok(Run { start : 8382238128741917860, actions : vec![(Action::NextRound, 4761280334617038924), (Action::NextRound, 4307459230874888534), (Action::AddVertex, -1401184906700154449), (Action::AddVertex, -8358486048188273524)] }))
}

#[test]
fn parser_file_run() -> std::io::Result<()> {
    let mut file = File::open("/Volumes/Emmanuel/state.edge")?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    match edge_parser::file(&contents) {
        Err(_) => Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "Unable to parse")),
        Ok(m) => {
            //println!("{:#?}", m);
            Ok(())
        }
    }
}