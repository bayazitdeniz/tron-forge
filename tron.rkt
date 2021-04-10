#lang forge
option problem_type temporal
option max_tracelength 20

abstract sig Idx {
    // right or below
    next: lone Idx
}
one sig I1, I2, I3, I4, I5, I6, I7 extends Idx {}

pred indexConnect {
    next = I1->I2 + I2->I3 + I3->I4 + I4->I5 + I5->I6 + I6->I7
}

abstract sig Player {
    var row: one Idx,
    var col: one Idx
}
one sig P1, P2 extends Player {}

one sig Board {
    var walls: set Idx->Idx
}

pred initSmallRoom {
    // NOTE: walls all around the board => handled in transition?
    no walls

    P1.row = I1
    P1.col = I1

    P2.row = I7
    P2.col = I7

    indexConnect
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

pred traces {
    initSmallRoom
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

// run { initSmallRoom } //for exactly 2 Player
run { traces }

