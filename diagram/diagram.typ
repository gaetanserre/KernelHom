#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node
#import fletcher.shapes: circle, hexagon, house, trapezium, triangle

#set page(width: auto, height: auto, margin: 1pt)

#let blob(pos, label, tint: white, ..args) = node(
  pos,
  align(center, text(fill: black, label)),
  width: auto,
  fill: white,
  stroke: 1pt + black,
  inset: 0.7em,
  shape: circle,
  ..args,
)

#set text(font: "New Computer Modern")
#show raw: set text(font: "FiraCode Nerd Font")
#show math.equation: set text(font: "New Computer Modern")

#let comp = text(size: 7pt, $times.o_k$)

#diagram(
  spacing: 8pt,
  cell-size: (8mm, 10mm),
  edge-stroke: 1pt + black,
  edge-corner-radius: 5pt,
  mark-scale: 70%,
  axes: (ltr, btt),

  blob((-2, 0), $X$),
  blob((2, 0), $Y$),
  blob((0, -1), $Z$),

  edge((-2, 0), (0, -1), "-|>", bend: -40deg, label-sep: 0em, label: $kappa$),
  edge((0, -1), (2, 0), "-|>", bend: -40deg, label-sep: 0em, label: $eta$),
  edge((-2, 0), (2, 0), "--|>", label-sep: 0em, label: $kappa gt.double eta$),

  node((-2, -2), text(size: 7.7pt, $X times X$), stroke: 1pt + black, inset: 2pt, shape: circle),
  blob((2, -2), text(size: 14pt, $I$)),

  edge((-2, 0), (-2, -2), "=>", `copy`, label-sep: 0.3em, label-angle: 90deg, mark-scale: 120%),
  edge((2, 0), (2, -2), "-/-|>", `delete`, label-sep: 0.3em, label-side: left, label-angle: 90deg, label-pos: 50%),
  edge((-2, -2), (2, -2), "-/-|>", `delete`, label-sep: 0.3em),
)
