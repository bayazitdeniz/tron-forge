#lang forge
option problem_type temporal
option max_tracelength 20

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

// TODO: change fixed player start?
pred initFirstAndLast {
    no walls
    --
    P1.row = FirstIdx
    P1.col = FirstIdx
    --
    P2.row = LastIdx
    P2.col = LastIdx
}

fun otherPlayer[p : Player] : Player {
    Player - p
}

pred switchPlayers {
    Board.(currPlayer') = otherPlayer[Board.currPlayer]
}

pred moveTo[p: Player, nextRow: Idx, nextCol: Idx] {
    // pre-conditions
    // some next loc - next relation is lone!
    some nextRow
    some nextCol
    // no wall in the next location
    not (nextRow->nextCol in Board.walls)
    // no player in the next location
    let otherP = otherPlayer[p] | {
        nextRow != otherP.row
        nextCol != otherP.col
    }

    // post-conditions
    // curr loc will be in walls
    Board.(walls') = Board.walls + (p.row->p.col)

    row' = (row - p->Idx) + p->nextRow
    col' = (col - p->Idx) + p->nextCol
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

pred loserStutter[p : Player] {
    let r = p.row | 
        let c = p.col | 
            let adjacents = (r.next)->c + (next.r)->c + r->(c.next) + r->(next.c) - none->Idx - Idx->none |
                let oP = otherPlayer[p]|
                    no (adjacents - Board.walls - (oP.row)->(oP.col))
    walls' = walls
    row' = row 
    col' = col
    currPlayer' = currPlayer
}

pred traces {
    always (
        moveUp[Board.currPlayer] or moveDown[Board.currPlayer] or moveLeft[Board.currPlayer] or moveRight[Board.currPlayer]
        or loserStutter[Board.currPlayer]
    )
}

inst threeByThreeBoard {
    Idx = I1 + I2 + I3
    FirstIdx = I1
    LastIdx = I3
    next = I1->I2 + I2->I3
}

inst fourByFourBoard {
    Idx = I1 + I2 + I3 + I4
    FirstIdx = I1
    LastIdx = I4
    next = I1->I2 + I2->I3 + I3->I4
}

inst sevenBySevenBoard {
    Idx = I1 + I2 + I3 + I4 + I5 + I6 + I7
    FirstIdx = I1
    LastIdx = I7
    next = I1->I2 + I2->I3 + I3->I4 + I4->I5 + I5->I6 + I6->I7
}

run { initFirstAndLast and traces } for fourByFourBoard

// TODO: predicate for wellFormed board ??