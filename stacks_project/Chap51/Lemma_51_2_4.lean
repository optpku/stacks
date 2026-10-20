/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.SubmonoidColimit
import StacksCheckRecall

universe u

open CategoryTheory Limits

/- Lemma 51.2.4 (1): if localizing `M` at `S` gives zero, the canonical
degree-zero local-cohomology colimit comparison is an isomorphism. -/
@[stacks 0DWT] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.zeroComparisonIsIso :
    {A : Type u} → [CommRing A] → (S : Submonoid A) → (M : ModuleCat A) →
      [Subsingleton (LocalizedModule S M)] →
      (RΓ : (f : S.Divisibility) →
        DerivedCategory (ModuleCat A) ⥤
          DerivedCategory.IdealPowerTorsion (Ideal.span {(f : A)})) →
      (hRΓ : ∀ f : S.Divisibility,
        DerivedCategory.IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f) →
      IsIso (CategoryTheory.DerivedCategory.LocalCohomology.zeroComparison S M RΓ hRΓ))

/- Lemma 51.2.4 (2): if localizing `M` at `S` gives zero, the degree-one
local-cohomology colimit is zero. -/
@[stacks 0DWT] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.colimitDegreeOneIsZero :
    {A : Type u} → [CommRing A] → (S : Submonoid A) → (M : ModuleCat A) →
      [Subsingleton (LocalizedModule S M)] →
      (RΓ : (f : S.Divisibility) →
        DerivedCategory (ModuleCat A) ⥤
          DerivedCategory.IdealPowerTorsion (Ideal.span {(f : A)})) →
      (hRΓ : ∀ f : S.Divisibility,
        DerivedCategory.IdealPowerTorsion.inclusion (Ideal.span {(f : A)}) ⊣ RΓ f) →
      IsZero (colimit
        (CategoryTheory.DerivedCategory.LocalCohomology.divisibilityDiagram S M RΓ hRΓ 1)))
