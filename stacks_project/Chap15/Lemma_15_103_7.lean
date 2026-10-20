/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.LocalizationAway

/-!
# Lemma 15.103.7

@stack 0H85
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory

universe u

/- Lemma 15.103.7 (0H85): a nonpositive derived module is a flat module in degree zero when
this holds after localization away from `f` and after reduction modulo `f`.  The shared owner is
general in the single degree and uses `IsFlatInDegree`; the definition unfolds to the exact
flat-module-and-isomorphism formulation displayed here. -/

@[stacks 0H85 "Lemma 15.103.7"]
#check fun {R : Type u} [CommRing R] (f : R)
    (M : DerivedCategory (ModuleCat R))
    (hM : M.IsLE 0)
    (hAway :
      ∃ N : ModuleCat (Localization.Away f), Module.Flat (Localization.Away f) N ∧
        IsIsomorphic
          ((ModuleCat.derivedExtensionOfScalars
            (algebraMap R (Localization.Away f))).obj M)
          ((DerivedCategory.singleFunctor (ModuleCat (Localization.Away f)) 0).obj N))
    (hQuot :
      ∃ N : ModuleCat (R ⧸ Ideal.span (Set.singleton f)),
        Module.Flat (R ⧸ Ideal.span (Set.singleton f)) N ∧
          IsIsomorphic
            ((ModuleCat.derivedExtensionOfScalars
              (algebraMap R (R ⧸ Ideal.span (Set.singleton f)))).obj M)
            ((DerivedCategory.singleFunctor
              (ModuleCat (R ⧸ Ideal.span (Set.singleton f))) 0).obj N)) ↦
  (DerivedCategory.IsFlatInDegree.of_localizationAway_of_quotient
    M f hM hAway hQuot :
      ∃ N : ModuleCat R, Module.Flat R N ∧
        IsIsomorphic M ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj N))

#check @DerivedCategory.IsFlatInDegree
#check @DerivedCategory.hasTorAmplitudeLE_iff_isLE
#check @DerivedCategory.hasTorAmplitudeIn_self_iff_isFlatInDegree
#check @DerivedCategory.HasTorAmplitudeGE.of_localizationAway_of_quotient
#check @DerivedCategory.HasTorAmplitudeIn.of_isLE_of_localizationAway_of_quotient
#check @DerivedCategory.IsFlatInDegree.of_localizationAway_of_quotient
