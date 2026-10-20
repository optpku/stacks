/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Projective.CompleteLocal
import StacksCheckRecall

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

/- Lemma 76.43.6: Let `(A, m, κ)` be a complete Noetherian local ring, and let
`X` be an algebraic space over `Spec(A)`. If `SchemeRealization.toBase X` is proper and
`dimension (AdicThickening.stage X (IsLocalRing.maximalIdeal A) 1) ≤ 1`,
identifying the stage at `1` with the special fibre
`X_κ = X ×_{Spec A} Spec(κ)`, then `X` is a scheme H-projective over `A`. -/
@[stacks 0AE7] #check
  (AlgebraicGeometry.AlgebraicSpace.isScheme_hProjective_of_proper_specialFiber_dimension_le_one :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Proper (SchemeRealization.toBase X)]
    (hdim : dimension (AdicThickening.stage X (IsLocalRing.maximalIdeal A) 1) ≤ 1),
    ∃ (T : Over (Spec (CommRingCat.of A))),
      Nonempty (X ≅ ofOver T) ∧ HProjective T.hom)
