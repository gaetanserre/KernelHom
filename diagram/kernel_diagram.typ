// `#kernel_diagram ProbabilityTheory.Kernel.swap_prod`, that is `swap β γ ∘ₖ (κ ×ₖ η) = η ×ₖ κ`.
// Compile with `typst compile diagram/kernel_diagram.typ diagram/kernel_diagram.svg`.

#import "template.typ": atom, kernel-diagram, obj

#set page(width: auto, height: auto, margin: 10pt, fill: white)

#kernel-diagram(
  lhs: (
    (
      (obj[α],),
      (atom[copy α],),
      (atom[κ], atom[η]),
      (atom[swap β γ],),
      (obj[γ], obj[β]),
    ),
    (
      ((0, 0), (1, 0)),
      ((1, 0), (2, 0)),
      ((1, 0), (2, 1)),
      ((2, 0), (3, 0)),
      ((2, 1), (3, 0)),
      ((3, 0), (4, 0)),
      ((3, 0), (4, 1)),
    ),
  ),
  rhs: (
    (
      (obj[α],),
      (atom[copy α],),
      (atom[η], atom[κ]),
      (obj[γ], obj[β]),
    ),
    (
      ((0, 0), (1, 0)),
      ((1, 0), (2, 0)),
      ((1, 0), (2, 1)),
      ((2, 0), (3, 0)),
      ((2, 1), (3, 1)),
    ),
  ),
)
