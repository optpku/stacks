/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.AdicCompletion.Frobenius
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Smooth.Cotangent

/-!
# Smooth complete local algebras for the Frobenius residue extension

The completion at the Frobenius coordinate relations is formally smooth and
induces bijective canonical cotangent maps. Every formally smooth complete local
algebra with the same base and residue extension has dimension at least the
number of coordinates.
-/

@[expose] public section

open CategoryTheory Algebra.H1Cotangent KaehlerDifferential MvRatFunc.Frobenius

noncomputable section

namespace CompleteLocalAlgCat

/-- The completion at the Frobenius coordinate relations, with its evaluation
residue identification, as a complete local algebra over the image subfield. -/
def pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    CompleteLocalAlgCat (baseField n p) (functionField n p) :=
  of (adicCompletion n p) (MvRatFunc.Frobenius.residueFieldIso n p)

/-- The carrier of the bundled Frobenius completion is the native adic completion. -/
theorem pthPowerAdicCompletion_carrier (n p : ℕ) [Fact p.Prime] :
    (pthPowerAdicCompletion n p).carrier = adicCompletion n p :=
  rfl

/-- The bundled Frobenius completion stores the quotient-induced residue identification. -/
theorem pthPowerAdicCompletion_residueFieldIso (n p : ℕ) [Fact p.Prime] :
    (pthPowerAdicCompletion n p).residueFieldIso =
      MvRatFunc.Frobenius.residueFieldIso n p :=
  rfl

/-- The Frobenius completion is formally smooth over the image subfield for
the topology defined by its maximal ideal. -/
theorem formallySmooth_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    (algebraMap (baseField n p) (pthPowerAdicCompletion n p).carrier).formally_smooth_for_adic
      (IsLocalRing.maximalIdeal (pthPowerAdicCompletion n p).carrier) :=
  sorry

/-- The restricted coyoneda of the Frobenius completion is smooth. -/
instance instIsSmooth_restrictedCoyoneda_pthPowerAdicCompletion
    (n p : ℕ) [Fact p.Prime] :
    Functor.IsSmooth (CategoryOfElements.π (restrictedCoyoneda (pthPowerAdicCompletion n p))) :=
  sorry

/-- The canonical map from first cotangent homology to the residue-kernel
cotangent of the Frobenius completion is bijective. -/
theorem bijective_toKerCotangent_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    Function.Bijective
      (toKerCotangent (baseField n p) (pthPowerAdicCompletion n p).carrier
        (functionField n p) (algebraMap_surjective (pthPowerAdicCompletion n p))) :=
  sorry

/-- The canonical Kähler base-change map of the Frobenius completion is bijective. -/
theorem bijective_mapBaseChange_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    Function.Bijective
      (mapBaseChange (baseField n p) (pthPowerAdicCompletion n p).carrier
        (functionField n p)) :=
  sorry

/-- Every formally smooth complete local algebra for the Frobenius-image
residue extension has dimension at least the number of coordinates. -/
theorem le_ringKrullDim_of_formallySmooth_frobenius (n p : ℕ) [Fact p.Prime]
    (R : CompleteLocalAlgCat (baseField n p) (functionField n p))
    (h_smooth : (algebraMap (baseField n p) R.carrier).formally_smooth_for_adic
      (IsLocalRing.maximalIdeal R.carrier)) :
    (n : WithBot ℕ∞) ≤ ringKrullDim R.carrier :=
  sorry

/-- The dimension of the Frobenius completion is at least the number of coordinates. -/
theorem le_ringKrullDim_pthPowerAdicCompletion (n p : ℕ) [Fact p.Prime] :
    (n : WithBot ℕ∞) ≤ ringKrullDim (pthPowerAdicCompletion n p).carrier :=
  sorry

end CompleteLocalAlgCat
