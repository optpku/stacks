/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologicalDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.5.8 (1): upper truncation induces an isomorphism on derived cohomology in
degrees at most the truncation bound. -/
@[stacks 08F7] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.upperTruncation_homologyMap_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Modules X ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesFiniteLimits F]
      [PreservesLimitsOfShape (Discrete ℕ) F]
      (N : ℕ), F.HasCohomologicalDimensionLEOn
        (quasiCoherentModuleProperty X) ((N : ℤ) - 1) →
      ∀ (E : DerivedQCoh X) (a i : ℤ), i ≤ a →
      IsIso
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
          ((KInjective.functor F).map
            ((t.truncLEι a).app ((inclusion X).obj E)))))

/- Lemma 75.5.8 (2): lower truncation at `b - N + 1` induces an isomorphism on derived
cohomology in degrees at least `b`. -/
@[stacks 08F7] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.lowerTruncation_homologyMap_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Modules X ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesFiniteLimits F]
      [PreservesLimitsOfShape (Discrete ℕ) F]
      (N : ℕ), F.HasCohomologicalDimensionLEOn
        (quasiCoherentModuleProperty X) ((N : ℤ) - 1) →
      ∀ (E : DerivedQCoh X) (b i : ℤ), b ≤ i →
      IsIso
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
          ((KInjective.functor F).map
            ((t.truncGEπ (b - (N : ℤ) + 1)).app ((inclusion X).obj E)))))

/- Lemma 75.5.8 (3): cohomology supported on `[a, b]` is sent to cohomology supported on
`[a, b + N - 1]`. -/
@[stacks 08F7] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightDerived_cohomology_isZero_outside :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Modules X ⥤ AddCommGrpCat.{u}) [F.Additive] [PreservesFiniteLimits F]
      [PreservesLimitsOfShape (Discrete ℕ) F]
      (N : ℕ), F.HasCohomologicalDimensionLEOn
        (quasiCoherentModuleProperty X) ((N : ℤ) - 1) →
      ∀ (E : DerivedQCoh X) (a b : EInt), a ≤ b →
      (∀ i : ℤ, (i : EInt) ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
          ((inclusion X).obj E))) →
      ∀ i : ℤ, (i : EInt) ∉
        Set.Icc a (b + (((N : ℤ) - 1 : ℤ) : EInt)) →
        IsZero
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
            ((KInjective.functor F).obj ((inclusion X).obj E))))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

end
