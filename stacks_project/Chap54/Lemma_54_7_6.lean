/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 54.7.6: in Situation 54.7.1, if `X` is normal and `A` is Nagata, then
the morphisms in `D(A)` from the residue field shifted by `-1` to `Rf_*𝒪_X` form a
subsingleton. Here `Rf_*𝒪_X` is viewed in `D(A)` using derived affine global sections. -/
@[stacks 0AXC] #check
  (AlgebraicGeometry.IsModification.homResidueFieldShift_negOne_subsingleton :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] [_root_.IsNormalRing A],
    ringKrullDim A = 2 → ∀ {X : Scheme.{u}}
      (f : X ⟶ Spec (.of A)) [IsModification f] (r : ℕ),
    (Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))) →
    X.isNormal →
    Subsingleton
      ((ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))⟦(-1 : ℤ)⟧ ⟶
        (Scheme.DerivedQCoh.affineGlobalSections (CommRingCat.of A)).obj
          ((Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj
            (Scheme.DerivedQCoh.structureSheaf X))))
