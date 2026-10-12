/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap81.Lemma_81_12_1_Glueable

/-!
# Lemma 81.12.1

For a Beauville-Laszlo glueing pair, glueability of global sections on affine
étale charts of an algebraic space over `Spec R` is equivalent to the same
condition for every affine étale test map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.12.1: for a Beauville-Laszlo glueing pair `(algebraMap R R', f)` and an
algebraic space `Y` over `X = Spec (CommRingCat.of R)`, existence of an étale covering
`Y_i ⟶ Y` by affine `ofOver (U i)` with glueable `Γ((U i).left, ⊤)` is equivalent to
`glueableGlobalSections R' f T` for every étale `φ : ofOver T ⟶ Y` with `T.left`
affine. -/
@[stacks 0F9P]
theorem exists_affineEtale_glueableGlobalSections_iff
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)
    [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (Y : AlgebraicSpace (Spec (CommRingCat.of R))) :
    (∃ (I : Type u) (_ : Small.{u} I)
        (U : I → Over (Spec (CommRingCat.of R)))
        (φ : ∀ i, ofOver (U i) ⟶ Y),
      (∀ i, AlgebraicGeometry.IsAffine (U i).left) ∧
        EtaleCovering (fun i ↦ Over.mk (φ i)) ∧
        ∀ i, Scheme.Hom.glueableGlobalSections R' f (U i)) ↔
      ∀ {T : Over (Spec (CommRingCat.of R))} [AlgebraicGeometry.IsAffine T.left]
        (φ : ofOver T ⟶ Y) [Etale φ],
        Scheme.Hom.glueableGlobalSections R' f T :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
