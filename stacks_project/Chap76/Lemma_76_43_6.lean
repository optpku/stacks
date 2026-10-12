/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap76.Lemma_76_43_1_AdicThickening

/-!
# Proper algebraic spaces of special-fibre dimension at most one

A proper algebraic space over the spectrum of a complete Noetherian local ring,
with special fibre of dimension at most one, is a scheme H-projective over the
base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.43.6: Let `(A, m, κ)` be a complete Noetherian local ring, and let
`X` be an algebraic space over `Spec(A)`. If `toBase X` is proper and
`dimension (AdicThickening.stage X (IsLocalRing.maximalIdeal A) 1) ≤ 1`,
identifying the stage at `1` with the special fibre
`X_κ = X ×_{Spec A} Spec(κ)`, then `X` is a scheme H-projective over `A`. -/
@[stacks 0AE7]
theorem isScheme_hProjective_of_proper_specialFiber_dimension_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Proper (toBase X)]
    (hdim : dimension (AdicThickening.stage X (IsLocalRing.maximalIdeal A) 1) ≤ 1) :
    ∃ (T : Over (Spec (CommRingCat.of A))),
      Nonempty (X ≅ ofOver T) ∧ HProjective T.hom :=
  sorry

/-- A proper algebraic space over a complete Noetherian local ring whose special
fibre has dimension at most one is a scheme. -/
theorem isScheme_of_proper_specialFiber_dimension_le_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Proper (toBase X)]
    (hdim : dimension (AdicThickening.stage X (IsLocalRing.maximalIdeal A) 1) ≤ 1) :
    IsScheme X :=
  sorry

/-- Any scheme representing a proper algebraic space over a complete Noetherian
local ring whose special fibre has dimension at most one is H-projective over
`Spec(A)`. -/
theorem hProjective_hom_of_iso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Proper (toBase X)]
    (hdim : dimension (AdicThickening.stage X (IsLocalRing.maximalIdeal A) 1) ≤ 1)
    {T : Over (Spec (CommRingCat.of A))} (e : X ≅ ofOver T) :
    HProjective T.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
