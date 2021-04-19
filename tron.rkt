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

pred validBoard {
    // next relation needs to be a list one beginning, one ending and everything connected
    FirstIdx->(Idx - FirstIdx) in ^next
    // players cannot be on a wall
    all p: Player | {
        not ((p.row)->(p.col) in Board.walls)
    }
    // players cannot be in the same location
    not((P1.row = P2.row) and (P1.col = P2.col))
}

pred traces {
    validBoard
    always (
        ((moveUp[Board.currPlayer] or moveDown[Board.currPlayer] or moveLeft[Board.currPlayer] or moveRight[Board.currPlayer]) and switchPlayers[currPlayer]) or loserStutter[Board.currPlayer]
    )
}

---------------------------------------------------------------------
-- Board Instances and Helpers
---------------------------------------------------------------------

-- Empty Boards
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

inst fourByFourEmptyBoard {
    Idx = I1 + I2 + I3 + I4
    FirstIdx = I1
    LastIdx = I4
    next = I1->I2 + I2->I3 + I3->I4
}

inst sevenBySevenEmptyBoard {
    Idx = I1 + I2 + I3 + I4 + I5 + I6 + I7
    FirstIdx = I1
    LastIdx = I7
    next = I1->I2 + I2->I3 + I3->I4 + I4->I5 + I5->I6 + I6->I7
}

-- Partial Boards
inst threeByThreeAlmostEndGame {
    Board = Board0
    Idx = I1 + I2 + I3
    FirstIdx = I1
    LastIdx = I3
    next = I1->I2 + I2->I3
    --
    walls ni Board0->(I1->I1) + Board0->(I2->I1) + Board0->(I3->I1) + Board0->(I3->I3) + Board0->(I2->I3) + Board0->(I1->I3)
    walls in Board->Idx->Idx
}

inst threeByThreeEndGame {
    Board = Board0
    Idx = I1 + I2 + I3
    FirstIdx = I1
    LastIdx = I3
    next = I1->I2 + I2->I3
    --
    walls ni Board0->(I1->I1) + Board0->(I2->I1) + Board0->(I3->I1) + Board0->(I3->I2) + Board0->(I3->I3) + Board0->(I2->I3) + Board0->(I1->I3)
    walls in Board->Idx->Idx
}

inst fourByFourPartFilledBoard {
    Board = Board0
    Idx = I1 + I2 + I3 + I4
    FirstIdx = I1
    LastIdx = I4
    next = I1->I2 + I2->I3 + I3->I4
    --
    walls ni Board0->(I2->I2) + Board0->(I2->I3)
    walls in Board->Idx->Idx
}

---------------------------------------------------------------------
-- Initializations and Endings
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

pred initFirstAndLastSomeWalls {
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

pred p2LosesLater {
    not (after after after loserStutter[P2])
    eventually loserStutter[P2]
}

---------------------------------------------------------------------
-- Running Experiments
---------------------------------------------------------------------

-- Empty Board Runs
// run { p1First and initFirstAndLast and traces } for twoByTwoEmptyBoard
// run { p1First and initFirstAndLast and traces } for threeByThreeEmptyBoard
// run { p1First and initFirstAndLast and traces } for fourByFourEmptyBoard
// run { p1First and initFirstAndLast and traces } for sevenBySevenEmptyBoard

-- EndGame or Partial Boards runs to debug transitions
// run { p2First and traces } for threeByThreeEndGame
// run { p1First and traces } for threeByThreeAlmostEndGame
// run { p1First and initFirstAndLastSomeWalls and traces and p2LosesLater } for fourByFourPartFilledBoard

---------------------------------------------------------------------
-- Basic Tests
---------------------------------------------------------------------
option verbose 0

test expect {
    moveUpTest: {
        some p: Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I3
                p.col = I3
                no walls

                -- second state
                p.row' = I2
                p.col' = I3
                Board.walls' = I3->I3

                -- third state
                p.row'' = I1
                p.col'' = I3
                Board.walls'' = I3->I3 + I2->I3

                -- transitions
                moveUp[p]
                after moveUp[p]
            }
        }
	} is sat

    noWallMoveUpTest: {
        some p: Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I3
                p.col = I3
                no walls

                -- second state
                p.row' = I2
                p.col' = I3
                no walls'

                -- transitions
                moveUp[p]
            }
        }
	} is unsat

    moveDownTest: {
        some p: Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I1
                p.col = I1
                no walls

                -- second state
                p.row' = I2
                p.col' = I1
                Board.walls' = I1->I1

                -- third state
                p.row'' = I3
                p.col'' = I1
                Board.walls'' = I1->I1 + I2->I1

                -- transitions
                moveDown[p]
                after moveDown[p]
            }
        }
	} is sat

    incorrectWallMoveDownTest: {
        some p: Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I1
                p.col = I1
                no walls

                -- second state
                p.row' = I2
                p.col' = I1
                Board.walls' = I2->I2

                -- transitions
                moveDown[p]
            }
        }
	} is unsat

    moveLeftTest: {
        some p: Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I3
                p.col = I3
                no walls

                -- second state
                p.row' = I3
                p.col' = I2
                Board.walls' = I3->I3

                -- third state
                p.row'' = I3
                p.col'' = I1
                Board.walls'' = I3->I3 + I3->I2

                -- transitions
                moveLeft[p]
                after moveLeft[p]
            }
        }
	} is sat

    noWallMoveLeftTest: {
        some p: Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I3
                p.col = I3
                no walls

                -- second state
                p.row' = I3
                p.col' = I2
                no walls'

                -- transitions
                moveLeft[p]
            }
        }
	} is unsat

    moveRightTest: {
        some p : Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I1
                p.col = I1
                no walls

                -- second state
                p.row' = I1
                p.col' = I2
                Board.walls' = I1->I1

                -- third state
                p.row'' = I1
                p.col'' = I3
                Board.walls'' = I1->I1 + I1->I2

                -- transitions
                moveRight[p]
                after moveRight[p]
            }
        }
    } is sat

    incorrectWallMoveRightTest: {
        some p : Player | {
            some I1, I2, I3: Idx | {
                next = I1->I2 + I2->I3
                validBoard

                -- first state
                p.row = I1
                p.col = I1
                no walls

                -- second state
                p.row' = I1
                p.col' = I2
                Board.walls' = I3->I3
                I1->I1 not in Board.walls'

                -- transitions
                moveRight[p]
            }
        }
    } is unsat

    switchPlayerTest: { 
        some I1, I2, I3: Idx | {
            next = I1->I2 + I2->I3
            no walls
            validBoard
            p1First

            -- first state
            P1.row = I1
            P1.col = I1
            P2.row = I3
            P2.col = I3
            Board.currPlayer = P1

            -- second state
            P1.row' = I1
            P1.col' = I2
            P2.row' = I3
            P2.col' = I3
            Board.currPlayer' = P2

            -- third state
            P1.row'' = I1
            P1.col'' = I2
            P2.row'' = I2
            P2.col'' = I3
            Board.currPlayer'' = P2

            -- transitions
            moveRight[P1]
            switchPlayers[currPlayer]
            after moveUp[P2]
            not switchPlayers[currPlayer']
        }
    } is sat

    endTest: { 
        // a two by two board game example where the starting player loses.
        some I1, I2: Idx | {
                next = I1->I2
                no walls
                validBoard
                p1First

                -- first state
                P1.row = I1
                P1.col = I1
                P2.row = I2
                P2.col = I2
                Board.currPlayer = P1

                -- second state
                P1.row' = I2
                P1.col' = I1
                P2.row' = I2
                P2.col' = I2
                Board.currPlayer' = P2

                -- third state
                P1.row'' = I2
                P1.col'' = I1
                P2.row'' = I1
                P2.col'' = I2
                Board.currPlayer'' = P1

                -- fourth state
                P1.row''' = I2
                P1.col''' = I1
                P2.row''' = I1
                P2.col''' = I2
                Board.currPlayer''' = P1

                -- transitions
                moveDown[P1]
                switchPlayers[currPlayer]
                after moveUp[P2]
                switchPlayers[currPlayer']
                after after loserStutter[P1]
                after after loserStutter[P2]
                not switchPlayers[currPlayer'']
        }
    } is sat
}

---------------------------------------------------------------------
-- Verifications
---------------------------------------------------------------------
// Note: Verifying theorems with a board that is larger than three by three is VERY slow.
//       We advise not to do so and verify theorems with a three by three board or a larger board with many walls.

test expect {
    vacuity1: { p1First and initFirstAndLast and traces } is sat
    vacuity2: { p2First and initFirstAndLast and traces } is sat
    -- Check it if it's possible for game to terminate and for the starting player to lose/the other to win
    aWinner1: { p1First and initFirstAndLast and traces and eventually loserStutter[Board.currPlayer]} is sat
    aWinner2: { p2First and initFirstAndLast and traces and eventually loserStutter[Board.currPlayer]} is sat
    -- Stronger verification: guarantee that someone will always lose / within the limits of a threeByThreeBoard
    alwaysSomeLoser: { (p1First and initFirstAndLast and traces) implies (eventually (some p: Player | loserStutter[p]))} for threeByThreeEmptyBoard is theorem
    -- Check if board ever changes or anything non-valid happens with transitions
    alwaysValidBoard1: {(p1First and initFirstAndLast and traces) implies (always validBoard)} for threeByThreeEmptyBoard is theorem
    alwaysValidBoard2: {(p2First and initFirstAndLast and traces) implies (always validBoard)} for twoByTwoEmptyBoard is theorem
}