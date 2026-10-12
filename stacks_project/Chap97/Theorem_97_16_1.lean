/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Bootstrapping algebraic stacks from an fppf algebraic-space atlas

If `S` is a scheme and `F : X ⟶ Y` is a 1-morphism of stacks in groupoids over
`(Sch/S)_fppf` such that `X` is representable by an algebraic space and `F` is
representable by algebraic spaces, surjective, flat, and locally of finite
presentation, then `Y` is an algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Theorem 97.16.1: Let `S` be a scheme. Let `F : X ⟶ Y` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `X` is representable by an
algebraic space, and `F` is representable by algebraic spaces, surjective,
flat and locally of finite presentation, then `Y` is an algebraic stack. The
hypotheses `Groupoids.Hom.Surjective`, `Groupoids.Hom.Flat`, and
`Groupoids.Hom.LocallyOfFinitePresentation` each include
`relativelyRepresentableByAlgebraicSpaces F`. -/
@[stacks 06DC]
theorem of_fppfAtlas {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y) (hX : IsRepresentableByAlgebraicSpace X)
    [Groupoids.Hom.Surjective F] [Groupoids.Hom.Flat F]
    [Groupoids.Hom.LocallyOfFinitePresentation F] :
    AlgebraicStack Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
