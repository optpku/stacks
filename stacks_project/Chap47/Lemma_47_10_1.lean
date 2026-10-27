/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 47.10.1 (1): the counit is an isomorphism on every derived object
with `I`-power-torsion cohomology. -/
@[stacks 0955] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.idealTorsionCounitAppIsIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (K : IdealPowerTorsion I),
      letI : Fact I.FG := ⟨Ideal.fg_of_isNoetherianRing I⟩
      IsIso ((CategoryTheory.DerivedCategory.LocalCohomology.idealTorsionCounit I
        (Ideal.fg_of_isNoetherianRing I)).app K.obj))

/- Lemma 47.10.1 (2): the canonical comparison functor is an equivalence. -/
@[stacks 0955] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.idealPowerTorsionDerivedComparisonIsEquivalence :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A),
      letI : Fact I.FG := ⟨Ideal.fg_of_isNoetherianRing I⟩
      (CohomologyIn.Comparison.functor
        (ModuleCat.isIdealPowerTorsion I : ObjectProperty (ModuleCat A))).IsEquivalence)

/- Lemma 47.10.1 (3): the comparison to a chosen closed-support right
adjoint is an isomorphism. -/
@[stacks 0955] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.idealToClosedSupportIsIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
      (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ),
      letI : Fact I.FG := ⟨Ideal.fg_of_isNoetherianRing I⟩
      IsIso (CategoryTheory.DerivedCategory.LocalCohomology.idealToClosedSupport I
        (Ideal.fg_of_isNoetherianRing I) RΓZ hRΓZ))

end CategoryTheory.DerivedCategory.LocalCohomology
