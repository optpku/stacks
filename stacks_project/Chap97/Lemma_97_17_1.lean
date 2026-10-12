/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Atlas of a flat locally finitely presented groupoid

If `(U, R, s, t, c)` is a groupoid in algebraic spaces whose source and
target maps are flat and locally of finite presentation, then the atlas
`G.atlas : G.U.left.toGroupoids ⟶ G.quotientStack` is flat, locally of
finite presentation, and surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 97.17.1 (1): let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`. Assume `s, t`
are flat and locally of finite presentation. Then the morphism
`G.atlas : G.U.left.toGroupoids ⟶ G.quotientStack` is flat. Formalized for a
groupoid `G` in algebraic spaces over an algebraic space `B` over `S`. -/
@[stacks 06FH, instance]
instance instFlat_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G] :
    Groupoids.Hom.Flat G.atlas :=
  sorry

/-- Lemma 97.17.1 (2): let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`. Assume `s, t`
are flat and locally of finite presentation. Then the morphism
`G.atlas : G.U.left.toGroupoids ⟶ G.quotientStack` is locally of finite
presentation. Formalized for a groupoid `G` in algebraic spaces over an
algebraic space `B` over `S`. -/
@[stacks 06FH, instance]
instance instLocallyOfFinitePresentation_atlas {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G] :
    Groupoids.Hom.LocallyOfFinitePresentation G.atlas :=
  sorry

/-- Lemma 97.17.1 (3): let `S` be a scheme contained in `Sch_fppf`. Let
`(U, R, s, t, c)` be a groupoid in algebraic spaces over `S`. Assume `s, t`
are flat and locally of finite presentation. Then the morphism
`G.atlas : G.U.left.toGroupoids ⟶ G.quotientStack` is surjective. Formalized
for a groupoid `G` in algebraic spaces over an algebraic space `B` over `S`. -/
@[stacks 06FH, instance]
instance instSurjective_atlas_of_flat {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Flat G] [LocallyOfFinitePresentation G] :
    Groupoids.Hom.Surjective G.atlas :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
