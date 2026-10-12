/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.LocalizedModule.Away

/-!
# Principal localization in `ModuleCat`

This thin categorical layer presents the elementary module-level
principal-localization criterion as an `IsZero` statement.
@stack 0H84
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.ModuleCat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Stacks 0H7N: a module object is zero when localization away from a
regular element is zero. -/
@[stacks 0H7N "ModuleCat vanishing by principal localization"]
theorem isZero_of_away_of_isSMulRegular {f : R}
    (hf : IsSMulRegular M f) (hAway : Subsingleton (LocalizedModule.Away f M)) :
    IsZero (ModuleCat.of R M) := sorry

/-- Multiplication by `f` is a monomorphism of module objects exactly when `f` acts
regularly on the underlying module. -/
@[stacks 0H84 "regular scalar action as a monomorphism"]
theorem mono_smul_id_iff_isSMulRegular (N : ModuleCat R) (f : R) :
    Mono (f • 𝟙 N) ↔ IsSMulRegular N f := sorry

namespace LocalizationAway

/-- A module object is zero when multiplication by `f` is monic and its localization
away from `f` is zero. -/
@[stacks 0H84 "module vanishing from a monic scalar and principal localization"]
theorem isZero_of_mono_smul (N : ModuleCat R) (f : R)
    (hmono : Mono (f • 𝟙 N))
    (hAway : IsZero
      (ModuleCat.of (Localization.Away f) (LocalizedModule.Away f N))) :
    IsZero N := sorry

end LocalizationAway

end CategoryTheory.ModuleCat
