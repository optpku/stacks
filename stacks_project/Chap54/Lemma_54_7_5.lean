/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.Cohomology
public import stacks_project.Chap54.Situation_54_7_1

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TopCat.Sheaf
open TopCat.Sheaf.Cohomology

universe u

/- Lemma 54.7.5: in Situation 54.7.1, if `X` is normal and `A` is Nagata, then
the restriction map `H¹(X, 𝒪_X) ⟶ H¹(f⁻¹(U), 𝒪_X)` to the inverse image of the
punctured spectrum is injective. -/
@[stacks 0AXB] #check
  (AlgebraicGeometry.IsModification.structureSheafH1_globalRestriction_mono :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A]
      [_root_.IsNormalRing A] (h_dimension : ringKrullDim A = 2) {X : Scheme.{u}}
      (f : X ⟶ Spec (.of A)) [IsModification f] (r : ℕ)
      (C : Fin r ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A)))
      (hX : X.isNormal),
      Mono (globalRestriction
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (SheafOfModules.unit X.ringCatSheaf)) 1
        (f ⁻¹ᵁ PuncturedSpectrum.puncturedOpen A)))
