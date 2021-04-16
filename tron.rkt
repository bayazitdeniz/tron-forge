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

// NOTE: cannot specify player location and walls in instance otherwise it doesn't var!

// inst threeByThreeEndGame {
//     Board = Board0
//     Idx = I1 + I2 + I3
//     FirstIdx = I1
//     LastIdx = I3
//     next = I1->I2 + I2->I3
//     Player = P10 + P20
//     P1 = P10 
//     P2 = P20
//     --
//     Board0->(I1->I1) + Board0->(I2->I1) + Board0->(I3->I1) + Board0->(I3->I3) + Board0->(I2->I3) + Board0->(I1->I3) in walls
//     -- 
//     P10->I3 + P20->I1 in row
//     P10->I2 + P20->I2 in col
// }

// inst threeByThreeAlmostEndGame {
//     Board = Board0
//     Idx = I1 + I2 + I3
//     FirstIdx = I1
//     LastIdx = I3
//     next = I1->I2 + I2->I3
//     Player = P10 + P20
//     P1 = P10 
//     P2 = P20
//     --
//     Board0->(I1->I1) + Board0->(I2->I1) + Board0->(I3->I1) + Board0->(I3->I2) + Board0->(I3->I3) + Board0->(I2->I3) + Board0->(I1->I3) in walls
//     --
//     P10->I2 + P20->I1 in row
//     P10->I2 + P20->I2 in col
// }

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

// inst fourByFourPartFilledBoard {
//     Board = Board0
//     Idx = I1 + I2 + I3 + I4
//     FirstIdx = I1
//     LastIdx = I4
//     next = I1->I2 + I2->I3 + I3->I4
//     walls = Board0->(I1->I2) + Board0->(I3->I3)
// }

// inst fiveByFiveFullyFilledBoard {
//     Board = Board0
//     Idx = I1 + I2 + I3 + I4 + I5
//     FirstIdx = I1
//     LastIdx = I5
//     next = I1->I2 + I2->I3 + I3->I4 + I4->I5
// }

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

---------------------------------------------------------------------
-- Running Experiments
---------------------------------------------------------------------

-- Empty Board Runs
// run { p1First and initFirstAndLast and traces } for twoByTwoEmptyBoard
run { p1First and initFirstAndLast and traces } for threeByThreeEmptyBoard
// run { p1First and initFirstAndLast and traces } for fourByFourEmptyBoard
// run { p1First and initFirstAndLast and traces } for sevenBySevenEmptyBoard

---------------------------------------------------------------------
-- Basic Tests
---------------------------------------------------------------------


// TODO: turn all of the partly filled with walls instances into tests,
//       the problem with partial maps is that if you specify walls 
//       it will consider them as static throughout the trace!
//       Why can't we put it in preds? Because we need the atoms specifying the Idx

-- EndGame runs to debug transitions
// run { p2First and traces } for threeByThreeEndGame
// run { p1First and traces } for threeByThreeAlmostEndGame
// run { p1First and traces } for threeByThreeAlmostEndGame2
// run { hardCodedSwitch and initFirstAndLast and traces } for threeByThreeEmptyBoard
// run { initFirstAndLast and traces } for fourByFourPartFilledBoard
// run { initFirstAndLast and traces } for fiveByFiveFullyFilledBoard

test expect {
    upAndDownTest: {
		some I1, I2, I3: Idx | {
            next = I1->I2 + I2->I3
            no walls

			-- first state
			Player.row = I1
            Player.col = I1

			-- second state
			Player.row' = I2
			Player.col' = I1

			-- third state
			Player.row'' = I3
			Player.col'' = I1

			-- fourth state
			Player.row''' = I2
			Player.col''' = I1

			-- transitions
			moveDown[Player]
			after moveDown[Player]
			//after after moveUp[Player] -- erroring on moveUp
		}
	} is sat

    leftAndRightTest: { 
        some I1, I2, I3: Idx | {
            next = I1->I2 + I2->I3
            no walls

			-- first state
			Player.row = I1
            Player.col = I1

			-- second state
			Player.row' = I1
			Player.col' = I2

			-- third state
			Player.row'' = I1
			Player.col'' = I3

			-- fourth state
			Player.row''' = I1
			Player.col''' = I2

			-- transitions
			moveRight[Player]
			after moveRight[Player]
			//after after moveLeft[Player] -- erroring when moving left
        }
        
    } is sat

    upTest: {
		some I1, I2, I3: Idx | {
            next = I1->I2 + I2->I3
            no walls

			-- first state
			Player.row = I3
            Player.col = I3

			-- second state
			Player.row' = I2
			Player.col' = I3

			-- third state
			Player.row'' = I1
			Player.col'' = I3

			-- transitions
			moveUp[Player]
			after moveUp[Player]

		}
	} is sat

     leftTest: {
		some I1, I2, I3: Idx | {
            next = I1->I2 + I2->I3
            no walls

			-- first state
			Player.row = I3
            Player.col = I3

			-- second state
			Player.row' = I3
			Player.col' = I2

			-- third state
			Player.row'' = I3
			Player.col'' = I1

			-- transitions
			moveLeft[Player]
			after moveLeft[Player]

		}
	} is sat
}

---------------------------------------------------------------------
-- Verifications
---------------------------------------------------------------------

test expect {
    vacuity: { p1First and initFirstAndLast and traces } is sat
}

---------------------------------------------------------------------
-- Future Work
---------------------------------------------------------------------
// TODO: predicate for wellFormed board ?
// TODO: change fixed player start?
// TODO: addition to viz to show who is currPlayer?