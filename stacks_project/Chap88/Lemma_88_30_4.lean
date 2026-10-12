/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap71.Lemma_71_19_3_AdmissibleBlowup
public import stacks_project.Chap88.Lemma_88_30_1_BaseChange

/-!
# Domination of proper 88.30.0.1 objects by admissible blowups

A proper object of the 88.30.0.1 category over a Noetherian local ring
`(A, maximalIdeal A)` is dominated by a `U`-admissible blowup of `specOver hA`,
where `U` is the complement of `V(maximalIdeal A)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.completionAlong

/-- The open subspace `U = Spec(A) \ V(maximalIdeal A)` of `specOver hA`. -/
abbrev maximalIdealComplement {A : Type u} [CommRing A] [IsLocalRing A]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) : OpenSubspace (specOver hA) :=
  OpenSubspace.ofOpens
    (openComplement (specOver hA) (zeroLocusPoints hA (maximalIdeal A)))

/-- The underlying point-set of `maximalIdealComplement hA` is the complement of
`V(maximalIdeal A)` in the points of `specOver hA`. -/
theorem maximalIdealComplement_pointsSet {A : Type u} [CommRing A] [IsLocalRing A]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    (maximalIdealComplement hA).pointsSet =
      (zeroLocusPoints hA (maximalIdeal A) : Set (Points (specOver hA)))ᶜ :=
  sorry

/-- Lemma 88.30.4: Let `(A, maximalIdeal A)` be a Noetherian local ring. Let
`f : X ⟶ S` be an object of 88.30.0.1 such that `f` is proper. Then there
exists a `U`-admissible blowup `S' ⟶ S` which dominates `X`. Here `S` is
`specOver hA`, an object of 88.30.0.1 is
`Y : Source (specOver hA) (zeroLocusPoints hA (maximalIdeal A))`, `X` is
`Y.obj.left`, `f` is `Y.obj.hom`, and `U = maximalIdealComplement hA`. A
`U`-admissible blowup is `AlgebraicSpace.IsAdmissibleBlowup (maximalIdealComplement hA) b`.
Domination means there is a factorization `S' ⟶ X ⟶ S` of the blowup morphism,
i.e. `g ≫ Y.obj.hom = b`. This is the special case of Lemma 76.39.5 for a
Noetherian local affine base. -/
@[stacks 0AE6]
theorem exists_isAdmissibleBlowup_dominating {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {S : Scheme.{u}}
    (hA : Spec (.of A) ⟶ S)
    (Y : Source (specOver hA) (zeroLocusPoints hA (maximalIdeal A)))
    [Proper Y.obj.hom] :
    ∃ (S' : AlgebraicSpace S) (b : S' ⟶ specOver hA) (g : S' ⟶ Y.obj.left),
      AlgebraicGeometry.AlgebraicSpace.IsAdmissibleBlowup (maximalIdealComplement hA) b ∧
        g ≫ Y.obj.hom = b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.completionAlong
