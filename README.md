# tron-forge
An implementation of the Tron game in Forge.

**Prompt: You should write a one page README describing how you structured your model and what your model proved. You can assume that anyone reading it will be familiar with your project proposal.**

## Game Description
We built a basic version of the Tron game from CS1410's final project (http://cs.brown.edu/courses/csci1410/assignments/tron.pdf). Quoting from that assignment spec: Tron-141 is a two-player, alternating-move, zero-sum game played on a walled-in rectangular grid (i.e., the board), in which players take turns moving straight ahead, left, or right, leaving behind an impenetrable barrier. A player loses by colliding with a barrier or a wall.
We chose Tron because it has an interesting visualization component, and we feel that it would be possible to model in Forge (for small boards, at least).

## Model Design Choices


### Sigs:
- **Idx**: Represents the indices and locations of the board. ex) In a 3x3 board, I1 -> I1 is the top left corner while I3 -> I3 is the bottom right corner.
- **Player**: Models a player in Tron. Each player has a row and column variable that indicates its current position on the board.
- **Board**: Models a Board in Tron. The board updates its set of walls as Players create them. It also keeps track of the current Player that is making a move.

### Predicates:
- **moveTo**: Defines how a player moves up, down, left, or right on the board.
- **loserStutter**: The losing case where the player is trapped and has no possible moves to make.
- **switchPlayers**: Changes the current player who should be making a move on the board.
- **validBoard**: Defines a valid board (connected, no players at same position, etc.)

### Traces: 
- In each valid step of the trace, a player can moves a certain direction and there is a switch in current player or the game ends.

## Tests & Verifications:
- Tests each move direction 
- Tests that a move into an index with a wall is unsat
- Tests that the Board switches players correctly
- Tests that the game correctly ends when the starting players loses
- Verifies that there is generally a valid trace when player1 or player2 starts
- Verifies that it's possible for game to terminate and for the starting player to lose/the other to win
- Verifies that someone will always lose / within the limits of a threeByThreeBoard
- Verifies if the board ever changes or anything non-valid happens with transitions

### Board Instances:
- Models empty, partial (one player is about to lose), and ending instances of boards of sizes 3x3, 4x4, and 7x7.

### Initilizations:
1. Running statements on empty and partially full boards.
2. Basic tests to check our transition predicates (both wheats and chaffs).
3. Verifications for stronger statements such as "someone will always lose".

## Visualization Description
*How should we understand an instance of your model and what your custom visualization shows?*


## Assumptions
*What assumptions did you make about scope? What are the limits of your model?*
- We limited the scope to mainly 3x3 and 4x4 boards. We found that verifying largers boards is extremely slow and thus our model cannot accurately depict a more realistic version of the Tron game where the boards give the players more area and options to move. Additionally, we narrowed the scope of the game to one without powerups. 


## Tradeoffs
*What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?*
- We did a lot of maneuvering around of variables when defining the Sigs of the game representation. We ultimately found that the Board keeping track of walls and the current Player while the Player itself keeps track of its current position would allow us the greatest ease and flexbility in defining our predicates. 

## Change in Goals
*Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?*

- We achieved what we layed out in the foundation of our proposal. However, we did not have enough time to implement the powerups and we were also limited to small boards because larger boards would take too much time to verify and run on Forge.
