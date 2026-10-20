/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Localization.Away
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-amplitude detected by a principal localization

The lower-bound gluing theorem is stated independently of the degree-zero
flat-module presentation.  This keeps localization, quotient, and flatness
bridges available as separate downstream ingredients.

@stack 066N
@stack 0H85
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

variable {R : Type u} [CommRing R]

/- The finite-cover form is kept in the Tor-amplitude owner so chapter entries do not depend on
one another for a reusable localization criterion. -/
/-- Lemma 15.67.16 (066N): Tor-amplitude descends from a finite principal-localization cover
whose generators span the unit ideal. -/
@[stacks 066N "finite localization-away Tor-amplitude criterion"]
theorem HasTorAmplitudeIn.of_finite_localizationAway
    {ι : Type*} [Finite ι]
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ)
    (hloc : ∀ i,
      HasTorAmplitudeIn (R := Localization.Away (f i))
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away (f i)))).obj K) a b) :
    HasTorAmplitudeIn (R := R) K a b := sorry
/- Proof strategy: for each degree-zero tensor test and each degree outside `[a, b]`, localize
its homology module at every `f i`; the unit-ideal cover hypothesis reflects simultaneous
vanishing back to the original module. -/

/-- A lower Tor-amplitude bound can be checked after localizing away from `f`
and after passing to the principal quotient by `f`. -/
@[stacks 0H85 "principal-localization lower Tor-amplitude criterion"]
theorem HasTorAmplitudeGE.of_localizationAway_of_quotient
    (M : DerivedCategory (ModuleCat R)) (f : R) {a : ℤ}
    (hAway :
      HasTorAmplitudeGE (R := Localization.Away f)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away f))).obj M) a)
    (hQuot :
      HasTorAmplitudeGE (R := R ⧸ Ideal.span (Set.singleton f))
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (R ⧸ Ideal.span (Set.singleton f)))).obj M) a) :
    HasTorAmplitudeGE (R := R) M a := sorry
/- Proof strategy: use the principal localization/quotient gluing triangle for each tensor test;
the two assumed lower bounds and the t-structure two-out-of-three theorem give the lower bound
over `R`. -/

/-- If `M` is already bounded above, the principal-localization criterion
upgrades lower bounds on the two base changes to a Tor-amplitude interval. -/
@[stacks 0H85 "bounded principal-localization Tor-amplitude criterion"]
theorem HasTorAmplitudeIn.of_isLE_of_localizationAway_of_quotient
    (M : DerivedCategory (ModuleCat R)) (f : R) {a b : ℤ}
    (hM : M.IsLE b)
    (hAway :
      HasTorAmplitudeGE (R := Localization.Away f)
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (Localization.Away f))).obj M) a)
    (hQuot :
      HasTorAmplitudeGE (R := R ⧸ Ideal.span (Set.singleton f))
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap R (R ⧸ Ideal.span (Set.singleton f)))).obj M) a) :
    HasTorAmplitudeIn (R := R) M a b := sorry
/- Proof strategy: obtain the lower endpoint from
`HasTorAmplitudeGE.of_localizationAway_of_quotient`, turn `hM` into the upper Tor-amplitude bound,
and combine both endpoints. -/

/-- Lemma 15.103.7 (0H85), generalized to any single degree: flatness in one
degree descends from the principal localization and principal quotient under
the corresponding upper cohomological bound. -/
@[stacks 0H85 "flat degree detected by a principal localization and quotient"]
theorem IsFlatInDegree.of_localizationAway_of_quotient
    (M : DerivedCategory (ModuleCat R)) (f : R) {n : ℤ}
    (hM : M.IsLE n)
    (hAway : IsFlatInDegree
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap R (Localization.Away f))).obj M) n)
    (hQuot : IsFlatInDegree
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap R (R ⧸ Ideal.span (Set.singleton f)))).obj M) n) :
    IsFlatInDegree M n := sorry
/- Proof strategy: translate both local flat-degree hypotheses to zero-width Tor-amplitude,
apply `HasTorAmplitudeIn.of_isLE_of_localizationAway_of_quotient` with `a = b = n`, and translate
the resulting interval back with `hasTorAmplitudeIn_self_iff_isFlatInDegree`. -/

end CategoryTheory.DerivedCategory
