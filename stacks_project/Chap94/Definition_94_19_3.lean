module

public import stacks_project.Chap94.Definition_94_19_3_BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- Definition 94.19.3: let `Sch_fppf` be a big fppf site, and let `g : S ⟶ S'` be
a morphism of this site. If `X'` is an algebraic stack over `S'`, then the
change of base of `X'` is the algebraic stack `X'_S` over `S` given by
`AlgebraicStack.baseChange g X'`. Its underlying category is the 2-fibre
product `(Sch/S)_fppf ×_{(Sch/S')_fppf} X'`, with structure morphism the first
projection to `(Sch/S)_fppf`. -/
@[stacks 04X7] #check AlgebraicGeometry.AlgebraicStack.baseChange
