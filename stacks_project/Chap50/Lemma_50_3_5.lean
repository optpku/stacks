/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open RingedSite.Hom RingedSite.Hom.DerivedAdjunction
open RingedSite.Hom.DerivedBaseChange RingedSite.Hom.ModuleDerived
open RingedSpace.ModuleDerived.Cohomology
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- Compatibility name for the derived pushforward base-change morphism of a relative form. -/
noncomputable abbrev pushforwardFormBaseChangeMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g) (p : ℕ) :
    (RingedSpace.modulePullbackDerived g.toShHom).obj
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (Λ[p] Ω[f.toShHom]))) ⟶
      (RingedSpace.moduleDerivedPushforward f'.toShHom).obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj
          (Λ[p] Ω[f'.toShHom])) :=
  DerivedPushforward.pushforwardFormBaseChangeMap g' f' f g sq p

/-- Compatibility name for the derived pushforward base-change morphism of the relative de Rham
complex. -/
noncomputable abbrev pushforwardDerivedComplexBaseChangeMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u}
        (DerivedPushforward.pushforwardHom f'))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f')))]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
    [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f')]
    (sq : IsPullback g' f' f g) :
    (modulePullbackDerived.{u} (DerivedPushforward.basePullbackHom g)).obj
        ((modulePushforwardDerived.{u} (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f)) ⟶
      (modulePushforwardDerived.{u} (DerivedPushforward.pushforwardHom f')).obj
        (DerivedPushforward.derivedComplex f') :=
  DerivedPushforward.pushforwardDerivedComplexBaseChangeMap g' f' f g sq

/- Lemma 50.3.5 (1): for a proper smooth morphism, every relative differential form has
perfect derived pushforward. -/
@[stacks 0FM0] #check
  (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardForm_isPerfect :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (p : ℕ),
      RingedSpace.ModuleDerived.IsPerfect
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (Λ[p] Ω[f.toShHom]))))

/- Lemma 50.3.5 (2): formation of the derived pushforward of a relative differential form
commutes with every cartesian base change. -/
@[stacks 0FM0] #check
  (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardForm_baseChange_isIso :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      [Smooth f] [IsProper f]
      [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
      [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
      (sq : IsPullback g' f' f g) (p : ℕ),
      IsIso (DerivedPushforward.pushforwardFormBaseChangeMap g' f' f g sq p))

/- Lemma 50.3.5 (3): the derived direct image of the relative de Rham complex is perfect. -/
@[stacks 0FM0] #check
  (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardDerivedComplex_isPerfect :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u} (DerivedPushforward.pushforwardHom f))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
          ((Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace).map f)))],
      IsPerfect.{u, u, u}
        ((modulePushforwardDerived.{u} (DerivedPushforward.pushforwardHom f)).obj
          (DerivedPushforward.derivedComplex f)))

/- Lemma 50.3.5 (4): formation of the derived direct image of the relative de Rham complex
commutes with every cartesian base change. -/
@[stacks 0FM0] #check
  (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardDerivedComplex_baseChange_isIso :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      [Smooth f] [IsProper f]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u} (DerivedPushforward.pushforwardHom f))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
          ((Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace).map f)))]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u} (DerivedPushforward.pushforwardHom f'))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
          ((Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace).map f')))]
      [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f)]
      [DerivedAdjunction.HasPair.{u} (DerivedPushforward.pushforwardHom f')]
      (sq : IsPullback g' f' f g),
      IsIso (DerivedPushforward.pushforwardDerivedComplexBaseChangeMap
        g' f' f g sq))

end AlgebraicGeometry.Scheme.DeRham
