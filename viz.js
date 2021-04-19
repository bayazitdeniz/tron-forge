const COLORS = {
  P1: "#0074D9",
  P2: "#FF4136",
};
const color = (name, s) => `<span style="color: ${COLORS[name]}">${s}</span>`;

const toNum = (idx) => +idx.id().slice(1).replace(/0$/, "") - 1;
const unwrap = (reln) => reln.tuples()[0].atoms()[0];
const getPos = (player, inst) =>
  [inst.field("row"), inst.field("col")]
    .map(player.join.bind(player))
    .map(unwrap)
    .map(toNum);

const indices = Idx.subSignatures()
  .map((idx) => idx.atoms()[0])
  .concat(Idx.atoms())
  .sort((a, b) => toNum(a) - toNum(b));

function render(instance, currentInstance) {
  const previousInstances = instances.slice(0, currentInstance);

  const board = Array(indices.length)
    .fill()
    .map(() => Array(indices.length).fill(" "));
  const fillPos = ([row, col], value) => (board[row][col] = value);

  Board0.join(walls)
    .tuples()
    .forEach((t) => fillPos(t.atoms().map(toNum), "#"));

  for (const inst of previousInstances) {
    fillPos(getPos(inst.signature("P1").atoms()[0], inst), color("P1", "#"));
    fillPos(getPos(inst.signature("P2").atoms()[0], inst), color("P2", "#"));
  }

  fillPos(
    getPos(instance.signature("P1").atoms()[0], instance),
    color("P1", "1")
  );
  fillPos(
    getPos(instance.signature("P2").atoms()[0], instance),
    color("P2", "2")
  );

  const border = "#".repeat(indices.length + 2);
  return [border, ...board.map((l) => `#${l.join("")}#`), border].join("\n");
}

div.innerHTML = "";

const pre = document.createElement("pre");
pre.style.display = "inline-block";
pre.style.margin = "2em";
pre.innerHTML = render(instance, currentInstance);
div.append(pre);

const pre2 = document.createElement("pre");
pre2.style.display = "inline-block";
pre2.innerHTML = render(instances[instances.length - 1], instances.length - 1);
div.append(pre2);

