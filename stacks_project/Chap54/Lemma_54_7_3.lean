/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.ComponentFactorization

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 54.7.3: in the non-isomorphism case of Situation 54.7.1, some nonzero
element of the maximal ideal of `A` has, at a closed point belonging only to each
chosen irreducible component of the closed fibre, a factorization whose first factor
lies in the stalk maximal ideal and remains nonzero in the reduced component stalk. -/
@[stacks 0AX9] #check
(AlgebraicGeometry.IsModification.existsNonzeroComponentFactorizations :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsModification f] (h_noniso : ¬ IsIso f) (r : ℕ)
    (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))),
    ∃ f₀ ∈ IsLocalRing.maximalIdeal A, f₀ ≠ 0 ∧
      ∀ i, ∃ (x : f.fiber (IsLocalRing.closedPoint A))
          (hx : x ∈ (C i : Set (f.fiber (IsLocalRing.closedPoint A)))),
        x ∈ closedPoints (f.fiber (IsLocalRing.closedPoint A)) ∧
          (∀ j, j ≠ i → x ∉ (C j : Set (f.fiber (IsLocalRing.closedPoint A)))) ∧
          ∃ gᵢ fᵢ : X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint A) x),
            ((StructureSheaf.toStalk A (f (f.fiberι (IsLocalRing.closedPoint A) x)) ≫
                f.stalkMap (f.fiberι (IsLocalRing.closedPoint A) x)) f₀ = gᵢ * fᵢ) ∧
              gᵢ ∈ IsLocalRing.maximalIdeal
                (X.presheaf.stalk (f.fiberι (IsLocalRing.closedPoint A) x)) ∧
              ((f.fiberι (IsLocalRing.closedPoint A)).stalkMap x ≫
                  ((f.fiber (IsLocalRing.closedPoint A)).irreducibleComponentSubschemeι
                    (C i)).stalkMap ⟨x, hx⟩) gᵢ ≠ 0)
