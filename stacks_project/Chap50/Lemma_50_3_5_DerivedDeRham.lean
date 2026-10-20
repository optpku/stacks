module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- Compatibility name for the canonical direct-image coefficient square. -/
noncomputable abbrev pushforwardSquare {X S : Scheme.{u}} (f : X ⟶ S) :=
  DerivedPushforward.pushforwardSquare f

/-- Compatibility name for the canonical direct-image coefficient morphism. -/
noncomputable abbrev pushforwardHom {X S : Scheme.{u}} (f : X ⟶ S) :=
  DerivedPushforward.pushforwardHom f

/-- Compatibility name for the localized relative de Rham complex. -/
noncomputable abbrev derivedComplex {X S : Scheme.{u}} (f : X ⟶ S) :=
  DerivedPushforward.derivedComplex f

/-- Compatibility name for the coefficient morphism of a cartesian square. -/
noncomputable abbrev pullbackHom {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :=
  DerivedPushforward.pullbackHom sq

/-- Compatibility name for the base coefficient square. -/
theorem baseSquare {S' S : Scheme.{u}} (g : S' ⟶ S) :
    CommSq g (𝟙 S') (𝟙 S) g :=
  DerivedPushforward.baseSquare g

/-- Compatibility name for the base-pullback coefficient morphism. -/
noncomputable abbrev basePullbackHom {S' S : Scheme.{u}} (g : S' ⟶ S) :=
  DerivedPushforward.basePullbackHom g

/-- Compatibility name for the coefficient square of a cartesian square. -/
theorem coefficientSquare {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    CommSq (pullbackHom sq) (pushforwardHom f')
      (pushforwardHom f) (basePullbackHom g) :=
  DerivedPushforward.coefficientSquare sq

/-- Compatibility name for equality of the two derived pullback composites. -/
theorem derivedPullbackComposite_eq {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    modulePullbackDerived.{u}
        ((pushforwardHom f').comp (basePullbackHom g)) =
      modulePullbackDerived.{u}
        ((pullbackHom sq).comp (pushforwardHom f)) :=
  DerivedPushforward.derivedPullbackComposite_eq sq

/-- Compatibility name for the canonical square isomorphism of pullback functors. -/
noncomputable def squareIso {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    modulePullbackDerived.{u} (basePullbackHom g) ⋙
          modulePullbackDerived.{u} (pushforwardHom f') ≅
      modulePullbackDerived.{u} (pushforwardHom f) ⋙
          modulePullbackDerived.{u} (pullbackHom sq) :=
  DerivedPushforward.squareIso sq

/-- Compatibility name for the extended relative de Rham comparison. -/
noncomputable def extendedDeRhamMap {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    (RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat ⟶
      (modulePushforwardComplex (pullbackHom sq)).obj
        ((RingedSpace.DeRham.complex f'.toLRSHom.toShHom).extend embeddingUpNat) :=
  DerivedPushforward.extendedDeRhamMap sq

/-- Compatibility name for the pullback-side de Rham comparison. -/
noncomputable def deRhamPullbackComplexComparison
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    (modulePullbackComplex (pullbackHom sq)).obj
        ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat) ⟶
      (RingedSpace.DeRham.complex f'.toLRSHom.toShHom).extend embeddingUpNat :=
  DerivedPushforward.deRhamPullbackComplexComparison sq

/-- Compatibility name for the localization of the relative de Rham homotopy category. -/
theorem coefficientLocalization_isLocalization {X S : Scheme.{u}} (f : X ⟶ S) :
    (moduleLocalization.{u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).IsLocalization
        (ModuleQis.{u}
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) :=
  DerivedPushforward.coefficientLocalization_isLocalization f

/-- Compatibility name for the derived relative de Rham comparison. -/
noncomputable def derivedDeRhamComparison
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (sq : IsPullback g' f' f g) :
    (modulePullbackDerived.{u} (pullbackHom sq)).obj (derivedComplex f) ⟶
      derivedComplex f' :=
  DerivedPushforward.derivedDeRhamComparison sq

end AlgebraicGeometry.Scheme.DeRham
