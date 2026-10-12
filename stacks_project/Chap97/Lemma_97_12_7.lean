/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap95.«95_18_2_1_Forgetful»
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap97.«97_5_0_1_OnObjects»

/-!
# Lemma 97.12.7

If `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`
that is representable by algebraic spaces and locally of finite presentation,
then the forgetful 1-morphism `forgetToY F d : H_d(𝒳/𝒴) ⟶ 𝒴` is limit
preserving on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.12.7: if `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over
`(Sch/S)_fppf` that is representable by algebraic spaces and locally of finite
presentation, then the forgetful 1-morphism
`p = forgetToY F d : stack (asGroupoidsOverMor F) d ⟶ 𝒴` is limit preserving on
objects. The hypothesis `Groupoids.Hom.LocallyOfFinitePresentation` includes
relative representability by algebraic spaces. -/
@[stacks 06CH]
instance forgetToY.limitPreservingOnObjects (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    Groupoids.Hom.LimitPreservingOnObjects (asGroupoidsOverMor (forgetToY F d)) :=
  sorry

/-- A directed affine inverse-limit problem for `forgetToY F d` admits a
solution making the restriction square commute. -/
theorem forgetToY.limitPreservingOnObjects_spec (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.LimitPreservingOnObjects (asGroupoidsOverMor (forgetToY F d))]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    (hD : ∀ i : I, IsAffine (D.obj i).left) (hpt : IsAffine c.pt.left)
    (i : I) (prob : Problem (asGroupoidsOverMor (forgetToY F d)) D c i) :
    ∃ cand : Candidate prob, IsSolution cand :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
