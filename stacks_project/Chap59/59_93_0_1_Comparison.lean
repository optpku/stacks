/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleVanishingCycles

#check (Coefficients : ∀ X : Scheme.{u}, Type (u + 2))
#check (Complexes : ∀ X : Scheme.{u}, Type (u + 2))
#check (unitObject : ∀ X : Scheme.{u}, X.Etale)
#check (coefficientsGrothendieck : ∀ X : Scheme.{u},
  IsGrothendieckAbelian.{u + 1} (Coefficients X))
#check (inverseImage : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  Coefficients Y ⥤ Coefficients X)
#check (AlgebraicGeometry.Scheme.Etale.Abelian.inverseImage_preservesFiniteLimits :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (inverseImage f))
#check (AlgebraicGeometry.Scheme.Etale.Abelian.inverseImage_preservesFiniteColimits :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (inverseImage f))
#check (derivedInverseImage : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  Complexes Y ⥤ Complexes X)
#check (sections : ∀ X : Scheme.{u}, Coefficients X ⥤ AddCommGrpCat.{u + 1})
#check (derivedSections : ∀ X : Scheme.{u},
  Complexes X ⥤ DerivedCategory AddCommGrpCat.{u + 1})

#check (unitToPullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  unitObject X ⟶ (smallEtalePullback f).obj (unitObject Y))

#check (sectionsPullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  sections Y ⟶ inverseImage f ⋙ sections X)
#check (derivedSectionsPullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  derivedSections Y ⟶ derivedInverseImage f ⋙ derivedSections X)
#check (derivedSectionsPullback_fac : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
  Cochain.unit (sections Y) ≫
      Functor.whiskerLeft (DerivedCategory.Q : CochainComplex (Coefficients Y) ℤ ⥤ _)
        (derivedSectionsPullback f) =
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (sectionsPullback f) (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex AddCommGrpCat.{u + 1} ℤ ⥤
        DerivedCategory AddCommGrpCat.{u + 1}) ≫
      Cochain.ExactFirst.unit (ExactFunctor.of (inverseImage f)) (sections X))
#check (InducedStrictHenselizationTriangle :
  ∀ {X S : Scheme.{u}} {RshS RshX : Type u} (f : X ⟶ S)
    (xbar : GeometricPoint X) [CommRing RshS]
    [Algebra (S.presheaf.stalk (xbar.map f).image) RshS]
    [IsStrictHenselizationOf (S.presheaf.stalk (xbar.map f).image) RshS]
    [CommRing RshX] [Algebra (X.presheaf.stalk xbar.image) RshX]
    [IsStrictHenselizationOf (X.presheaf.stalk xbar.image) RshX]
    (h : strictHenselizationScheme X xbar RshX ⟶
      strictHenselizationScheme S (xbar.map f) RshS), Prop)

end AlgebraicGeometry.Scheme.EtaleVanishingCycles
