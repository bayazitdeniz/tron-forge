const toNum = (idx) => +idx.id().slice(1, -1) - 1;
const unwrap = (reln) => reln.tuples()[0].atoms()[0];
const getPos = (player) =>
  [row, col].map(player.join.bind(player)).map(unwrap).map(toNum);
const fillPos = ([row, col], value) => (board[row][col] = value);

const indices = Idx.subSignatures()
  .map((idx) => idx.atoms()[0])
  .sort((a, b) => toNum(a) - toNum(b));

const board = Array(indices.length)
  .fill()
  .map(() => Array(indices.length).fill(" "));

fillPos(getPos(P1), "1");
fillPos(getPos(P2), "2");
Board0.join(walls)
  .tuples()
  .forEach((t) => fillPos(t.atoms().map(toNum), "#"));

const pre = document.createElement("pre");
const border = "#".repeat(indices.length + 2);
pre.textContent = [border, ...board.map((l) => `#${l.join("")}#`), border].join(
  "\n"
);
div.innerHTML = "";
div.append(pre);

debugger;
