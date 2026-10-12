/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation

/-!
# Quotient stacks of flat locally finitely presented groupoids

The quotient stack `[U / R]` associated to a groupoid in algebraic spaces
whose source and target are flat and locally of finite presentation is an
algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Theorem 97.17.2: let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`. Assume `s, t`
are flat and locally of finite presentation. Then the quotient stack
`[U / R]` is an algebraic stack over `S`. Formalized for a groupoid `G` in
algebraic spaces over an algebraic space `B` over `S`, with `[U / R]` as
`G.quotientStack`, source and target flat as `[Flat G]`, and source and
target locally of finite presentation as `[LocallyOfFinitePresentation G]`. -/
@[stacks 06FI, instance]
instance instAlgebraicStack_quotientStack_of_flat {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G] :
    AlgebraicStack G.quotientStack :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
