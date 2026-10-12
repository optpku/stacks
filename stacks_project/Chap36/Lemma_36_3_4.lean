/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologicalDimension
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.TStructure Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.3.4 (1): upper truncation induces an isomorphism on derived cohomology in
degrees at most the truncation bound. -/
@[stacks 08D4] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.upperTruncation_homologyMap_isIso :
    ∀ {X : Scheme.{u}}
      (F : X.toRingedSpace.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
      [PreservesLimitsOfShape (Discrete ℕ) F]
      (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ((N : ℤ) - 1))
      (E : DerivedQCoh X) (a i : ℤ), i ≤ a →
      IsIso
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
          ((KInjective.functor F).map
            ((t.truncLEι a).app ((inclusion X).obj E)))))

/- Lemma 36.3.4 (2): lower truncation at `b - N + 1` induces an isomorphism on derived
cohomology in degrees at least `b`. -/
@[stacks 08D4] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.lowerTruncation_homologyMap_isIso :
    ∀ {X : Scheme.{u}}
      (F : X.toRingedSpace.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
      [PreservesLimitsOfShape (Discrete ℕ) F]
      (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ((N : ℤ) - 1))
      (E : DerivedQCoh X) (b i : ℤ), b ≤ i →
      IsIso
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map
          ((KInjective.functor F).map
            ((t.truncGEπ (b - (N : ℤ) + 1)).app ((inclusion X).obj E)))))

/- Lemma 36.3.4 (3): cohomology supported on `[a, b]` is sent to cohomology supported on
`[a, b + N - 1]`. -/
@[stacks 08D4] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightDerived_cohomology_isZero_outside :
    ∀ {X : Scheme.{u}}
      (F : X.toRingedSpace.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
      [PreservesLimitsOfShape (Discrete ℕ) F]
      (N : ℕ) (hF : F.HasCohomologicalDimensionLEOn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ((N : ℤ) - 1))
      (E : DerivedQCoh X) (a b : EInt), a ≤ b →
      (∀ i : ℤ, (i : EInt) ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor X.toRingedSpace.Modules i).obj
          ((inclusion X).obj E))) →
      ∀ i : ℤ, (i : EInt) ∉
        Set.Icc a (b + (((N : ℤ) - 1 : ℤ) : EInt)) →
        IsZero
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
            ((KInjective.functor F).obj ((inclusion X).obj E))))

end AlgebraicGeometry.Scheme.DerivedQCoh

end
