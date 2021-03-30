#lang forge
option problem_type temporal

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

pred moveUp[player : Player] {
    // preconditions
    let nextRow = next.(player.row) | {
        // something above
        some nextRow
        // no wall above
        not (nextRow->(player.col) in Board.walls)

        // postconditions
        // curr loc will be in walls
        Board.(walls') = Board.walls + (player.row->player.col)
        // rowIdx change same column
        player.(row') = nextRow
        player.(col') = player.col
    }
}

pred traces {
    initSmallRoom
    moveUp[P2] until P2.row = I1
}

// run { indexConnect } //for exactly 2 Player
run { traces }

