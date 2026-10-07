module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_4_Smooth
public import stacks_project.Chap94.Definition_94_16_5_Quotient

/-!
# Quotient stacks of smooth groupoids

The quotient stack `[U / R]` associated to a smooth groupoid in algebraic
spaces is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Theorem 94.17.3: let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a smooth groupoid in algebraic spaces over `S`. Then the
quotient stack `[U / R]` is an algebraic stack over `S`. Formalized for a
smooth groupoid `G` in algebraic spaces over an algebraic space `B` over `S`,
with `[U / R]` as `G.quotientStack`. -/
@[stacks 04TK]
instance instAlgebraicStack_quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] :
    AlgebraicStack G.quotientStack :=
  sorry

/-- A smooth groupoid in algebraic spaces admits a scheme `W` over `S` and a
surjective smooth 1-morphism `GroupoidsOver.slice W ⟶ G.quotientStack`. This is
the atlas clause of `AlgebraicStack` for the quotient stack `[U / R]`. -/
theorem existsSmoothSurjectiveSchemeAtlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] :
    ∃ (W : Over S) (p : GroupoidsOver.slice W ⟶ G.quotientStack),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
