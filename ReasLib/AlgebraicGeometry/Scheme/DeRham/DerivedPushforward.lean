/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.Composition.KFlat
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.FlatCoefficients
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry
open RingedSite.Hom
open RingedSite.Hom.DerivedAdjunction
open RingedSite.Hom.DerivedBaseChange
open RingedSite.Hom.ModuleDerived
open RingedSpace.ModuleDerived.Cohomology
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.DerivedPushforward

-- Local instance justification (defeq pin): align the coefficient-site derived categories with the canonical localization used by `derivedComplex` and the total-derived counit.
attribute [local instance] moduleCat_hasDerivedCategory

/-- The square whose coefficient morphism is direct image along a scheme morphism. -/
noncomputable abbrev pushforwardSquare {X S : Scheme.{u}} (f : X ⟶ S) :
    CommSq f f (𝟙 S) (𝟙 S) :=
  CommSq.mk rfl

/-- The coefficient-site morphism along which the relative de Rham complex is pushed forward. -/
noncomputable abbrev pushforwardHom {X S : Scheme.{u}} (f : X ⟶ S) :=
  RingedSpace.DeRham.baseChangeHom
    ((pushforwardSquare f).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The relative de Rham complex, extended from nonnegative to integer degrees and localized to
the derived category of modules over `f⁻¹𝒪_S`. -/
noncomputable abbrev derivedComplex {X S : Scheme.{u}} (f : X ⟶ S) :
    RingedSite.Hom.ModuleDerived.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) :=
  (RingedSite.Hom.moduleLocalization
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).obj
      ((HomotopyCategory.quotient _ (up ℤ)).obj
        ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat))

/-- The cartesian-square coefficient morphism from the base-changed relative de Rham site to the
original relative de Rham site. -/
noncomputable abbrev pullbackHom {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :=
  RingedSpace.DeRham.baseChangeHom
    (sq.toCommSq.map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The square whose coefficient morphism is pullback along a map of base schemes. -/
theorem baseSquare {S' S : Scheme.{u}} (g : S' ⟶ S) :
    CommSq g (𝟙 S') (𝟙 S) g := sorry

/-- The coefficient-site morphism induced by a map of base schemes. -/
noncomputable abbrev basePullbackHom {S' S : Scheme.{u}} (g : S' ⟶ S) :=
  RingedSpace.DeRham.baseChangeHom
    ((baseSquare g).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The coefficient-site morphisms attached to a cartesian square form a commutative square. -/
theorem coefficientSquare {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    CommSq (pullbackHom sq) (pushforwardHom f')
      (pushforwardHom f) (basePullbackHom g) := sorry

/-- The two coefficient-site composites in a cartesian square induce the same derived pullback
functor. -/
theorem derivedPullbackComposite_eq {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    modulePullbackDerived.{u}
        ((pushforwardHom f').comp (basePullbackHom g)) =
      modulePullbackDerived.{u}
        ((pullbackHom sq).comp (pushforwardHom f)) := sorry

/-- The canonical square comparing the two composites of derived pullback functors attached to a
cartesian square of schemes. -/
noncomputable def squareIso {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    modulePullbackDerived.{u} (basePullbackHom g) ⋙
          modulePullbackDerived.{u} (pushforwardHom f') ≅
      modulePullbackDerived.{u} (pushforwardHom f) ⋙
          modulePullbackDerived.{u} (pullbackHom sq) :=
  @modulePullbackDerived.compIso _ _ _ (pushforwardHom f') (basePullbackHom g)
      _ _ _ _ _ _ _ _
      (modulePullbackDerived.compComparison_isIso
        (pushforwardHom f') (basePullbackHom g)) ≪≫
    eqToIso (derivedPullbackComposite_eq sq) ≪≫
    (@modulePullbackDerived.compIso _ _ _ (pullbackHom sq) (pushforwardHom f)
      _ _ _ _ _ _ _ _
      (modulePullbackDerived.compComparison_isIso
        (pullbackHom sq) (pushforwardHom f))).symm

/-- The de Rham map of a cartesian square, extended from nonnegative to integer degrees and
compared with direct image of the extended target complex. -/
noncomputable def extendedDeRhamMap {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat ⟶
      (modulePushforwardComplex (pullbackHom sq)).obj
        ((RingedSpace.DeRham.complex f'.toLRSHom.toShHom).extend embeddingUpNat) :=
  HomologicalComplex.extendMap
      (RingedSpace.DeRham.map (sq.toCommSq.map
        (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace))) embeddingUpNat ≫
    (embeddingUpNat.mapAppIso
      (modulePushforward.{u} (pullbackHom sq))
      (RingedSpace.DeRham.complex f'.toLRSHom.toShHom)).inv

/-- The pullback-side adjoint of the extended relative de Rham comparison. -/
noncomputable def deRhamPullbackComplexComparison
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    (modulePullbackComplex (pullbackHom sq)).obj
        ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat) ⟶
      (RingedSpace.DeRham.complex f'.toLRSHom.toShHom).extend embeddingUpNat :=
  (modulePullbackComplexHomEquiv.{u} (pullbackHom sq)
    ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat)
    ((RingedSpace.DeRham.complex f'.toLRSHom.toShHom).extend embeddingUpNat)).symm
      (extendedDeRhamMap sq)

/-- The canonical homotopy-to-derived functor for a relative de Rham coefficient site is a
localization at quasi-isomorphisms. -/
theorem coefficientLocalization_isLocalization {X S : Scheme.{u}} (f : X ⟶ S) :
    (moduleLocalization.{u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).IsLocalization
        (ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) := sorry

/-- The canonical comparison from derived pullback of the relative de Rham complex to the
relative de Rham complex of the base-changed morphism. -/
noncomputable def derivedDeRhamComparison
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    (modulePullbackDerived.{u} (pullbackHom sq)).obj (derivedComplex f) ⟶
      derivedComplex f' :=
  (@Functor.totalLeftDerivedCounit _ _ _ _ _ _
      (modulePullbackToDerived.{u} (pullbackHom sq))
      (moduleLocalization.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
      (coefficientLocalization_isLocalization f)
      (modulePullbackToDerived.hasLeftDerived (pullbackHom sq))).app
        ((HomotopyCategory.quotient _ (up ℤ)).obj
          ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat)) ≫
    (moduleLocalization.{u}
      (RingedSpace.DeRham.coefficientSite f'.toLRSHom.toShHom)).map
        ((HomotopyCategory.quotient _ (up ℤ)).map
          (deRhamPullbackComplexComparison sq))

/-- The perfectness of derived pushforward for every relative differential form of a proper smooth
morphism. -/
theorem pushforwardForm_isPerfect {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] (p : ℕ) :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (Λ[p] Ω[f.toShHom]))) := sorry

/-- The canonical derived base-change morphism for a relative differential form. -/
noncomputable def pushforwardFormBaseChangeMap
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
  ((Hom.DerivedBaseChange.map sq.toCommSq).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Λ[p] Ω[f.toShHom]))) ≫
    (RingedSpace.moduleDerivedPushforward f'.toShHom).map
      (singlePullbackComparison g'.toShHom
          (Λ[p] Ω[f.toShHom]) 0 ≫
        (DerivedCategory.singleFunctor X'.Modules 0).map
          (RelativeDifferentials.formComparison sq.toCommSq p))

/-- Formation of the derived pushforward of a relative differential form is invariant under
cartesian base change. -/
theorem pushforwardForm_baseChange_isIso
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [Smooth f] [IsProper f]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g) (p : ℕ) :
    IsIso (pushforwardFormBaseChangeMap g' f' f g sq p) := sorry

/-- The derived pushforward of the relative de Rham complex of a proper smooth morphism is
perfect. -/
theorem pushforwardDerivedComplex_isPerfect {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))] :
    IsPerfect.{u, u, u}
      ((modulePushforwardDerived.{u} (pushforwardHom f)).obj
        (derivedComplex f)) := sorry

/-- The canonical derived base-change morphism for the relative de Rham complex. -/
noncomputable def pushforwardDerivedComplexBaseChangeMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (pushforwardHom f'))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f')))]
    [DerivedAdjunction.HasPair.{u} (pushforwardHom f)]
    [DerivedAdjunction.HasPair.{u} (pushforwardHom f')]
    (sq : IsPullback g' f' f g) :
    (modulePullbackDerived.{u} (basePullbackHom g)).obj
        ((modulePushforwardDerived.{u} (pushforwardHom f)).obj
          (derivedComplex f)) ⟶
      (modulePushforwardDerived.{u} (pushforwardHom f')).obj
        (derivedComplex f') :=
  DerivedBaseChange.map
      (pullbackHom sq) (pushforwardHom f') (pushforwardHom f)
      (basePullbackHom g) (squareIso sq) (derivedComplex f) ≫
    (modulePushforwardDerived.{u} (pushforwardHom f')).map
      (derivedDeRhamComparison sq)

/-- Formation of the derived pushforward of the relative de Rham complex is invariant under
cartesian base change. -/
theorem pushforwardDerivedComplex_baseChange_isIso
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [Smooth f] [IsProper f]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (pushforwardHom f))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f)))]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u} (pushforwardHom f'))
      (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
        ((Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace).map f')))]
    [DerivedAdjunction.HasPair.{u} (pushforwardHom f)]
    [DerivedAdjunction.HasPair.{u} (pushforwardHom f')]
    (sq : IsPullback g' f' f g) :
    IsIso (pushforwardDerivedComplexBaseChangeMap g' f' f g sq) := sorry

end AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
