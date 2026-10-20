/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- 33.21.1.1: the completed local ring at a point of a locally Noetherian
scheme over a field is a quotient of a finite-variable formal power series ring
over its residue field, compatibly with the residue-field map. -/
@[stacks 0C53]
#check (AlgebraicGeometry.exists_residueField_mvPowerSeries_quotient_ringEquiv_completedStalk :
  ∀ {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsLocallyNoetherian X.left]
    (x : X.left),
    ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.left.residueField x)))
      (e : (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
          (X.left.presheaf.stalk x)),
        (((AlgebraicGeometry.Scheme.completedStalkResidueFieldMap X.left x).comp
          e.toRingHom).comp
            (algebraMap (X.left.residueField x)
              (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I))) =
          RingHom.id (X.left.residueField x))
