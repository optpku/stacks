/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.SurfaceModification

open CategoryTheory

universe u

open AlgebraicGeometry

/- Lemma 54.7.2: in Situation 54.7.1, the modification `f : X ⟶ Spec (.of A)` is
dominated by a blowup admissible over `PuncturedSpectrum.puncturedOpen A`. -/
@[stacks 0B4M] #check (AlgebraicGeometry.IsModification.exists_admissibleBlowup_dominating :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [_root_.IsNormalRing A]
      (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
      (f : X ⟶ Spec (.of A)) [IsModification f] (r : ℕ)
      (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))),
      ∃ (X' : Scheme.{u}) (b : X' ⟶ Spec (.of A)) (g : X' ⟶ X),
        IsAdmissibleBlowup (PuncturedSpectrum.puncturedOpen A) b ∧ g ≫ f = b)
