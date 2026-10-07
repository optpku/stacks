module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
public import ReasLib.Algebra.Module.Torsion.Functoriality
public import ReasLib.RingTheory.Completion.Flat

import Mathlib.Tactic.CrossRefAttribute

/-!
# Beauville-Laszlo glueing for flat principal-adic completion

Flatness identifies every finite torsion stage with its image in the principal-adic completion.
Consequently the completion and localization form a Beauville-Laszlo glueing pair.  Noetherian
rings satisfy the required flatness condition.

@stack 0BNT
-/

@[expose] public section

noncomputable section

universe u

namespace LocalizedModule.Away.BeauvilleLaszlo

variable {R : Type u} [CommRing R]

/-- The map from an `f ^ n`-torsion stage to the corresponding torsion stage in the
principal-adic completion. -/
@[stacks 0BNT "finite torsion comparison for principal-adic completion"]
noncomputable abbrev principalAdicCompletionTorsionByMap (f : R) (n : ℕ+) :
    Submodule.torsionBy R R (f ^ (n : ℕ)) →ₗ[R]
      Submodule.torsionBy R (principalAdicCompletion f) (f ^ (n : ℕ)) :=
  Submodule.torsionByMap (algebraMap R (principalAdicCompletion f)) (f ^ (n : ℕ))

/-- Remark 15.91.8 (1): flat principal-adic completion preserves every positive finite torsion
stage. -/
@[stacks 0BNT "Remark 15.91.8 (1)"]
theorem principalAdicCompletionTorsionByMap_bijective_of_flat
    (f : R) (hflat : (algebraMap R (principalAdicCompletion f)).Flat) (n : ℕ+) :
    Function.Bijective (principalAdicCompletionTorsionByMap f n) := sorry

/-- Remark 15.91.8 (2): flat principal-adic completion gives a Beauville-Laszlo glueing pair. -/
@[stacks 0BNT "Remark 15.91.8 (2)"]
theorem principalAdicCompletion_isGlueingPair_of_flat
    (f : R) (hflat : (algebraMap R (principalAdicCompletion f)).Flat) :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f := sorry

/-- Remark 15.91.8 (3): over a Noetherian ring, principal-adic completion preserves every
positive finite torsion stage. -/
@[stacks 0BNT "Remark 15.91.8 (3)"]
theorem principalAdicCompletionTorsionByMap_bijective_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) (n : ℕ+) :
    Function.Bijective (principalAdicCompletionTorsionByMap f n) := sorry

/-- Remark 15.91.8 (4): a Noetherian ring and its principal-adic completion form a
Beauville-Laszlo glueing pair. -/
@[stacks 0BNT "Remark 15.91.8 (4)"]
theorem principalAdicCompletion_isGlueingPair_of_isNoetherianRing
    [IsNoetherianRing R] (f : R) :
    IsBeauvilleLaszloGlueingPairAlong
      (algebraMap R (principalAdicCompletion f)) f := sorry

end LocalizedModule.Away.BeauvilleLaszlo
