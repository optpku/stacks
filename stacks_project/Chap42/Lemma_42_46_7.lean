/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Triangulated

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

open RingedSpace.ModuleDerived.Morphism

/- Lemma 42.46.7 (1): under any of the four stated representability or quasi-compactness
hypotheses, the Chern classes of the first object in the distinguished triangle are defined. -/
@[stacks 0F9F] #check (AlgebraicGeometry.ChernClass.Derived.isDefined_obj₁_of_distinguished :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X),
    IsDefined T.obj₁)

/- Lemma 42.46.7 (2): under any of the four stated representability or quasi-compactness
hypotheses, the Chern classes of the second object in the distinguished triangle are defined. -/
@[stacks 0F9F] #check (AlgebraicGeometry.ChernClass.Derived.isDefined_obj₂_of_distinguished :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X),
    IsDefined T.obj₂)

/- Lemma 42.46.7 (3): under any of the four stated representability or quasi-compactness
hypotheses, the Chern classes of the third object in the distinguished triangle are defined. -/
@[stacks 0F9F] #check (AlgebraicGeometry.ChernClass.Derived.isDefined_obj₃_of_distinguished :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X),
    IsDefined T.obj₃)

/- Lemma 42.46.7 (4): total Chern classes are multiplicative on the distinguished triangle,
so `c(T.obj₂) = c(T.obj₁) * c(T.obj₃)` in completed nonnegative Chow cohomology. -/
@[stacks 0F9F] #check (AlgebraicGeometry.ChernClass.Derived.totalClass_distinguished :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X),
    totalClass δ π classes T.obj₂ h₂
        (isDefined_obj₂_of_distinguished δ π T hT h₁ h₂ h₃ h) =
      totalClass δ π classes T.obj₁ h₁
          (isDefined_obj₁_of_distinguished δ π T hT h₁ h₂ h₃ h) *
        totalClass δ π classes T.obj₃ h₃
          (isDefined_obj₃_of_distinguished δ π T hT h₁ h₂ h₃ h))

/- Lemma 42.46.7 (5): Chern characters are additive on the distinguished triangle,
so `ch(T.obj₂) = ch(T.obj₁) + ch(T.obj₃)`. -/
@[stacks 0F9F] #check (AlgebraicGeometry.ChernClass.Derived.character_distinguished :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X),
    character δ π classes T.obj₂ h₂
        (isDefined_obj₂_of_distinguished δ π T hT h₁ h₂ h₃ h) =
      character δ π classes T.obj₁ h₁
          (isDefined_obj₁_of_distinguished δ π T hT h₁ h₂ h₃ h) +
        character δ π classes T.obj₃ h₃
          (isDefined_obj₃_of_distinguished δ π T hT h₁ h₂ h₃ h))

/- Lemma 42.46.7 (6): every degree-`p` Newton class is additive on the distinguished triangle,
so `P_p(T.obj₂) = P_p(T.obj₁) + P_p(T.obj₃)`. -/
@[stacks 0F9F] #check (AlgebraicGeometry.ChernClass.Derived.newtonClass_distinguished :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (T : Triangle (RingedSpace.ModuleDerived X.toRingedSpace))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived X.toRingedSpace))
    (h₁ : RingedSpace.ModuleDerived.IsPerfect T.obj₁)
    (h₂ : RingedSpace.ModuleDerived.IsPerfect T.obj₂)
    (h₃ : RingedSpace.ModuleDerived.IsPerfect T.obj₃)
    (h : (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsEnvelope f ∧
        HasLocallyBoundedFiniteLocallyFree
          ((RingedSpace.modulePullbackDerived f.toShHom).map T.mor₁)) ∨
      HasLocallyBoundedFiniteLocallyFree T.mor₁ ∨
      (∀ Z : irreducibleComponents X, IsCompact (Z : Set X)) ∨ CompactSpace X)
    (p : ℕ),
    newtonClass δ π classes T.obj₂ h₂
        (isDefined_obj₂_of_distinguished δ π T hT h₁ h₂ h₃ h) p =
      newtonClass δ π classes T.obj₁ h₁
          (isDefined_obj₁_of_distinguished δ π T hT h₁ h₂ h₃ h) p +
        newtonClass δ π classes T.obj₃ h₃
          (isDefined_obj₃_of_distinguished δ π T hT h₁ h₂ h₃ h) p)

end AlgebraicGeometry.ChernClass.Derived
