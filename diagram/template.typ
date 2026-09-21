// Template drawing string diagrams of kernels in the style of the `#kernel_diagram` command.
//
// A diagram is given by its rows, from top to bottom, and by its strings. A row is an array of
// nodes: `obj` for the objects at the boundary of the diagram and `atom` for the kernels. A string
// `((i, j), (k, l))` joins the `j`-th node of the row `i` to the `l`-th node of the row `k > i`.
// Unless a position `x` is given, a node is placed below the nodes of the previous rows it is
// joined to, or below the node with the same index in the previous row if there is none, without
// overlapping the other nodes of its row.

#let row-sep = 100
#let node-sep = 15
#let box-height = 30
#let box-inset = 9
#let min-box-width = 25
#let border-color = rgb("#98b2c0")
#let label-font = "FiraCode Nerd Font Mono"
#let title-font = "New Computer Modern"

#let atom(label, x: auto) = (label: label, atom: true, x: x)
#let obj(label, x: auto) = (label: label, atom: false, x: x)

#let layout(rows, strings, widths) = {
  let xs = ()
  for (i, row) in rows.enumerate() {
    let desired = row
      .enumerate()
      .map(((j, node)) => {
        if node.x != auto { return node.x }
        let parents = strings.filter(((a, b)) => b == (i, j)).map(((a, b)) => xs.at(a.at(0)).at(a.at(1)))
        if parents.len() > 0 { parents.sum() / parents.len() } else if i > 0 and j < xs.at(i - 1).len() {
          xs.at(i - 1).at(j)
        }
      })
    let pos = ()
    for (j, d) in desired.enumerate() {
      if j == 0 {
        pos.push(if d == none { 0 } else { d })
      } else {
        let min = pos.at(j - 1) + widths.at(i).at(j - 1) / 2 + node-sep + widths.at(i).at(j) / 2
        pos.push(if d == none { min } else { calc.max(d, min) })
      }
    }
    let placed = range(row.len()).filter(j => desired.at(j) != none)
    let shift = if placed.len() == 0 {
      -(pos.first() - widths.at(i).first() / 2 + pos.last() + widths.at(i).last() / 2) / 2
    } else {
      placed.map(j => desired.at(j) - pos.at(j)).sum() / placed.len()
    }
    xs.push(pos.map(x => x + shift))
  }
  xs
}

#let string-diagram(rows, strings, row-sep: row-sep) = context {
  let label(node) = text(font: label-font, size: 13pt, node.label)
  let widths = rows.map(row => row.map(node => calc.max(
    min-box-width,
    measure(label(node)).width / 1pt + 2 * box-inset,
  )))
  let xs = layout(rows, strings, widths)
  let bounds = xs
    .enumerate()
    .map(((i, row)) => row
      .enumerate()
      .map(((j, x)) => (
        x - widths.at(i).at(j) / 2,
        x + widths.at(i).at(j) / 2,
      )))
  let left = calc.min(..bounds.flatten().chunks(2).map(b => b.at(0)))
  let right = calc.max(..bounds.flatten().chunks(2).map(b => b.at(1)))
  let node-center(i, j) = ((xs.at(i).at(j) - left) * 1pt, (i * row-sep + box-height / 2) * 1pt)
  box(width: (right - left) * 1pt, height: ((rows.len() - 1) * row-sep + box-height) * 1pt, {
    for (a, b) in strings {
      place(line(start: node-center(..a), end: node-center(..b), stroke: 1pt + black))
    }
    for (i, row) in rows.enumerate() {
      for (j, node) in row.enumerate() {
        let (x, y) = node-center(i, j)
        let width = widths.at(i).at(j) * 1pt
        place(dx: x - width / 2, dy: y - box-height * 1pt / 2, box(
          width: width,
          height: box-height * 1pt,
          fill: white,
          stroke: if node.atom { 1pt + border-color } else { none },
          radius: if node.atom { 5pt } else { 12pt },
          align(center + horizon, label(node)),
        ))
      }
    }
  })
}

// The diagrams of both sides of an equality of kernels, as displayed by `#kernel_diagram`.
// `lhs` and `rhs` are pairs `(rows, strings)`.
#let kernel-diagram(lhs: none, rhs: none) = grid(
  columns: 2,
  column-gutter: 160pt,
  ..(lhs, rhs).map(d => align(center + top, string-diagram(..d))),
)
