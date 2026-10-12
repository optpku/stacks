/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap94.Definition_94_16_4_Smooth
public import stacks_project.Chap94.Definition_94_16_5_Quotient

/-!
# Smooth surjective atlas of a quotient stack

The atlas 1-morphism `𝒮_U ⟶ [U / R]` of a smooth groupoid in algebraic spaces
is a smooth surjective 1-morphism of categories fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 94.17.2 (1): let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a smooth groupoid in algebraic spaces over `S`. Then the
morphism `𝒮_U ⟶ [U / R]` is smooth. Formalized for a smooth groupoid `G` in
algebraic spaces over an algebraic space `B` over `S`, with `𝒮_U` as
`G.U.left.toGroupoids`, `[U / R]` as `G.quotientStack`, and the morphism as
`G.atlas`. -/
@[stacks 04X0]
instance instSmooth_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] :
    Groupoids.Hom.Smooth G.atlas :=
  sorry

/-- Lemma 94.17.2 (2): let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a smooth groupoid in algebraic spaces over `S`. Then the
morphism `𝒮_U ⟶ [U / R]` is surjective. Formalized for a smooth groupoid `G`
in algebraic spaces over an algebraic space `B` over `S`, with `𝒮_U` as
`G.U.left.toGroupoids`, `[U / R]` as `G.quotientStack`, and the morphism as
`G.atlas`. -/
@[stacks 04X0]
instance instSurjective_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] :
    Groupoids.Hom.Surjective G.atlas :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
