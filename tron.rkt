#lang forge
option problem_type temporal
option max_tracelength 30

---------------------------------------------------------------------
-- SIGS
---------------------------------------------------------------------
sig Idx {
    // right or below
    next: lone Idx
}
// minimum 2 Idx need to exist:
// these help to describe the init without having an explicit instance
one sig FirstIdx, LastIdx extends Idx {}

abstract sig Player {
    var row: one Idx,
    var col: one Idx
}
one sig P1, P2 extends Player {}

one sig Board {
    var walls: set Idx->Idx,
    var currPlayer: one Player
}

---------------------------------------------------------------------
-- Trace Transition Predicates
---------------------------------------------------------------------
fun otherPlayer[p : Player] : Player {
    Player - p
}

pred moveTo[p: Player, nextRow: Idx, nextCol: Idx] {
    // pre-conditions
    // some next loc - next relation is lone!
    some nextRow
    some nextCol
    // no wall in the next location
    not (nextRow->nextCol in Board.walls)
    // impossible but - not the player's current location
    (nextRow != p.row or nextCol != p.col)
    // no other player in the next location
    let otherP = otherPlayer[p] | (nextRow != otherP.row) or (nextCol != otherP.col)

    // post-conditions
    // curr loc will be in walls
    Board.(walls') = Board.walls + (p.row->p.col)

    row' = (row - p->(p.row)) + p->nextRow
    col' = (col - p->(p.col)) + p->nextCol
}

pred moveUp[p: Player] {
    moveTo[p, next.(p.row), p.col]
}

pred moveDown[p : Player] {
    moveTo[p, (p.row).next, p.col]
}

pred moveLeft[p: Player] {
    moveTo[p, p.row, next.(p.col)]
}

pred moveRight[p : Player] {
    moveTo[p, p.row, (p.col).next]
}

---------------------------------------------------------------------
-- Trace Stutter and Validity (switching players) Predicates
---------------------------------------------------------------------
pred loserStutter[p : Player] {
    let r = p.row | 
        let c = p.col | 
            let adjacents = (r.next)->c + (next.r)->c + r->(c.next) + r->(next.c) - none->Idx - Idx->none |
                let oP = otherPlayer[p] |
                    no (adjacents - Board.walls - (oP.row)->(oP.col))
    walls' = walls
    row' = row 
    col' = col
    currPlayer' = currPlayer
}

pred switchPlayers[curr : Board->Player] {
    Board.curr' = otherPlayer[Board.curr]
}

// pred testTraces {
//     moveUp[P2]
//     after moveLeft[P2]
//     after after moveDown[P2]
//     after after after moveLeft[P2]
//     after after after after moveUp[P2]
//     after after after after after moveUp[P2]
//     after after after after after after {
//         moveRight[P2]
//         until no P2.col.next
// }

pred traces {
    always (
        ((moveUp[Board.currPlayer] or moveDown[Board.currPlayer] or moveLeft[Board.currPlayer] or moveRight[Board.currPlayer]) and switchPlayers[currPlayer]) or loserStutter[Board.currPlayer]
    )
}

---------------------------------------------------------------------
-- Board Instances and Helpers
---------------------------------------------------------------------

inst twoByTwoEmptyBoard {
    Idx = I1 + I2
    FirstIdx = I1 
    LastIdx = I2
    next = I1->I2
}

inst threeByThreeEmptyBoard {
    Idx = I1 + I2 + I3
    FirstIdx = I1
    LastIdx = I3
    next = I1->I2 + I2->I3
}

inst threeByThreeAlmostEndGame {
    Board = Board0
    Idx = I1 + I2 + I3
    FirstIdx = I1
    LastIdx = I3
    next = I1->I2 + I2->I3
    Player = P10 + P20
    P1 = P10 
    P2 = P20
    --
    walls = Board0->(I1->I1) + Board0->(I2->I1) + Board0->(I3->I1) + 
            Board0->(I3->I3) + Board0->(I2->I3) + Board0->(I1->I3)
    -- 
    row = P10->I3 + P20->I1
    col = P10->I2 + P20->I2
}

inst threeByThreeEndGame {
    Board = Board0
    Idx = I1 + I2 + I3
    FirstIdx = I1
    LastIdx = I3
    next = I1->I2 + I2->I3
    Player = P10 + P20
    P1 = P10 
    P2 = P20
    --
    walls = Board0->(I1->I1) + Board0->(I2->I1) + Board0->(I3->I1) + Board0->(I3->I2) +
            Board0->(I3->I3) + Board0->(I2->I3) + Board0->(I1->I3) 
    -- 
    row = P10->I2 + P20->I1
    col = P10->I2 + P20->I2
}

inst fourByFourEmptyBoard {
    Idx = I1 + I2 + I3 + I4
    FirstIdx = I1
    LastIdx = I4
    next = I1->I2 + I2->I3 + I3->I4
}

// pred hardCodedSwitchForFour {
//     Board.currPlayer = P1
//     moveDown[P1]
//     Board.(currPlayer') = P2
//     after moveUp[P2]
//     Board.(currPlayer'') = P1
//     after after moveDown[P1]
//     Board.(currPlayer''') = P2
//     after after after moveUp[P2]
//     Board.(currPlayer'''') = P1
//     after after after after moveDown[P1]
//     Board.(currPlayer''''') = P2
//     after after after after after moveUp[P2]
//     Board.(currPlayer'''''') = P1
//     after after after after after after moveRight[P1]
// }

inst fourByFourPartFilledBoard {
    Board = Board0
    Idx = I1 + I2 + I3 + I4
    FirstIdx = I1
    LastIdx = I4
    next = I1->I2 + I2->I3 + I3->I4
    walls = Board0->(I1->I2) + Board0->(I3->I3)
}

inst fiveByFiveFullyFilledBoard {
    Board = Board0
    Idx = I1 + I2 + I3 + I4 + I5
    FirstIdx = I1
    LastIdx = I5
    next = I1->I2 + I2->I3 + I3->I4 + I4->I5
    walls = Board0->(Idx->Idx) - Board0->(FirstIdx->FirstIdx) - Board0->(LastIdx->LastIdx)
}

inst sevenBySevenEmptyBoard {
    Idx = I1 + I2 + I3 + I4 + I5 + I6 + I7
    FirstIdx = I1
    LastIdx = I7
    next = I1->I2 + I2->I3 + I3->I4 + I4->I5 + I5->I6 + I6->I7
}

---------------------------------------------------------------------
-- Initializations
---------------------------------------------------------------------

pred initFirstAndLast {
    no walls
    --
    P1.row = FirstIdx
    P1.col = FirstIdx
    --
    P2.row = LastIdx
    P2.col = LastIdx
}

pred p1First {
    Board.currPlayer = P1
}

pred p2First {
    Board.currPlayer = P2
}

// pred answer {
//     Board.currPlayer = P1
//     moveUp[P1]
//     Board.currPlayer' = P2
//     after (always loserStutter[P2])
// }

---------------------------------------------------------------------
-- Running Experiments
---------------------------------------------------------------------

// Empty Board Runs
run { p1First and initFirstAndLast and traces } for twoByTwoEmptyBoard
run { p1First and initFirstAndLast and traces } for threeByThreeEmptyBoard
run { p1First and initFirstAndLast and traces } for fourByFourEmptyBoard
run { p1First and initFirstAndLast and traces } for sevenBySevenEmptyBoard

// run { p2First and traces } for threeByThreeEndGame

// run { answer and traces } for threeByThreeAlmostEndGame

// run {p1FirstP2Second} for threeByThreeAlmostEndGame

// run { hardCodedSwitch and initFirstAndLast and traces } for threeByThreeEmptyBoard

// run { initFirstAndLast and traces } for fourByFourPartFilledBoard

// run { initFirstAndLast and traces } for fiveByFiveFullyFilledBoard

---------------------------------------------------------------------
-- Future Work
---------------------------------------------------------------------
// TODO: predicate for wellFormed board ?
// TODO: change fixed player start?
// TODO: addition to viz to show who is currPlayer?