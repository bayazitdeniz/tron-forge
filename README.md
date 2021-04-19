# tron-forge
An implementation of the Tron game in Forge.

**Prompt: You should write a one page README describing how you structured your model and what your model proved. You can assume that anyone reading it will be familiar with your project proposal.**

## Game Description
We built a basic version of the Tron game from CS1410's final project (http://cs.brown.edu/courses/csci1410/assignments/tron.pdf). Quoting from that assignment spec: Tron-141 is a two-player, alternating-move, zero-sum game played on a walled-in rectangular grid (i.e., the board), in which players take turns moving straight ahead, left, or right, leaving behind an impenetrable barrier. A player loses by colliding with a barrier or a wall.
We chose Tron because it has an interesting visualization component, and we feel that it would be possible to model in Forge (for small boards, at least).

## Model Design Choices


### Sigs:
- **Idx**: 
- **Player**:
- **Board**:

### Predicates:
- **moveTo**:
- **loserStutter**:
- **switchPlayers**:
- **validBoard**:

### Traces:

## Tests & Verifications:

### Board Instances:
### Initilizations:
1. Running statements on empty and partially full boards.
2. Basic tests to check our transition predicates (both wheats and chaffs).
3. Verifications for stronger statements such as "someone will always lose".

## Visualization Description
*How should we understand an instance of your model and what your custom visualization shows?*

## Assumptions
*What assumptions did you make about scope? What are the limits of your model?*

## Tradeoffs
*What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?*

## Change in Goals
*Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?*

We achieved what we layed out in the foundation of our proposal.
