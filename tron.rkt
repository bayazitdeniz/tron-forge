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
    var walls: set Idx->Idx
}

pred initFirstAndLast {
    no walls
    --
    P1.row = FirstIdx
    P1.col = FirstIdx
    --
    P2.row = LastIdx
    P2.col = LastIdx
}   

pred moveTo[player: Player, nextRow: Idx, nextCol: Idx] {
    // something above
    some nextRow
    some nextCol
    // no wall above
    not (nextRow->nextCol in Board.walls)

    // postconditions
    // curr loc will be in walls
    Board.(walls') = Board.walls + (player.row->player.col)

    row' = (row - player->Idx) + player->nextRow
    col' = (row - player->Idx) + player->nextCol
}

pred moveUp[player: Player] {
    moveTo[player, next.(player.row), player.col]
}

pred moveDown[player : Player] {
    moveTo[player, (player.row).next, player.col]
}

pred moveLeft[player: Player] {
    moveTo[player, player.row, next.(player.col)]
}

pred moveRight[player : Player] {
    moveTo[player, player.row, (player.col).next]
}

pred winnerStutter {
    // todo!
}

pred traces {
    moveUp[P2]
    after moveLeft[P2]
    after after moveDown[P2]
    after after after moveLeft[P2]
    after after after after moveUp[P2]
    after after after after after moveUp[P2]
    after after after after after after {
        moveRight[P2]
        until no P2.col.next
    }
}

inst sevenBySevenBoard {
    Idx = I1 + I2 + I3 + I4 + I5 + I6 + I7
    FirstIdx = I1
    LastIdx = I7
    next = I1->I2 + I2->I3 + I3->I4 + I4->I5 + I5->I6 + I6->I7
}

// run { initSmallRoom } //for exactly 2 Player
run { initFirstAndLast and traces } for sevenBySevenBoard
