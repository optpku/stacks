/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap94.Definition_94_12_2_Etale
public import stacks_project.Chap97.Theorem_97_17_2
public import stacks_project.Chap101.Lemma_101_32_2_OpenSubgroupoid

/-!
# Open subgroupoids induce étale surjective maps of quotient stacks

If `(U, R, s, t, c)` is a groupoid in algebraic spaces with `s, t` flat and
locally of finite presentation, and `P ⊂ R` is an open subspace making
`(U, P, s|_P, t|_P, c)` a groupoid, then `[U / P] ⟶ [U / R]` is a morphism of
algebraic stacks which is representable by algebraic spaces, surjective, and
étale in the sense of Algebraic Stacks, Definition 94.10.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid

/-- Lemma 101.32.2 (1): let `S` be a scheme. Let `(U, R, s, t, c)` be a groupoid
in algebraic spaces over `S`. Assume `s, t` are flat and locally of finite
presentation. Let `P ⊂ R` be an open subspace such that
`(U, P, s|_P, t|_P, c)` on `P ×_{s, U, t} P` is a groupoid in algebraic spaces
over `S`. Then `[U / P] ⟶ [U / R]` is a morphism of algebraic stacks which is
representable by algebraic spaces. -/
@[stacks 0DU2]
theorem relativelyRepresentableByAlgebraicSpaces_quotientHom {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    [Flat G] [LocallyOfFinitePresentation G] :
    relativelyRepresentableByAlgebraicSpaces H.quotientHom :=
  sorry

/-- Lemma 101.32.2 (2): under the same hypotheses, `[U / P] ⟶ [U / R]` is
surjective in the sense of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 0DU2]
instance instSurjective_quotientHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    [Flat G] [LocallyOfFinitePresentation G] :
    Groupoids.Hom.Surjective H.quotientHom :=
  sorry

/-- Lemma 101.32.2 (3): under the same hypotheses, `[U / P] ⟶ [U / R]` is étale
in the sense of Algebraic Stacks, Definition 94.10.1. -/
@[stacks 0DU2]
instance instEtale_quotientHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    [Flat G] [LocallyOfFinitePresentation G] :
    Groupoids.Hom.Etale H.quotientHom :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid
