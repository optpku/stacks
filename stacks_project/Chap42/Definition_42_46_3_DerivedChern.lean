/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Derived

#check (AlgebraicGeometry.ChernClass.Derived.existsUniqueDerivedTotalClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E)),
    ∃! cE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p,
      ∀ {Y : Scheme.{u}} (f : Y ⟶ X) [IsEnvelope f]
        (K : CochainComplex Y.Modules ℤ)
        (hRep : IsIsomorphic (DerivedCategory.Q.obj K)
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
        (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
        (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
        (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (p : ℕ),
        ChowCohomology.restrictDegree δ
            (Over.homMk f : Over.mk (f ≫ π) ⟶ Over.mk π) (p : ℤ) (cE p) =
          Complex.totalClass δ (f ≫ π) (classes.reanchor (Over.mk (f ≫ π)))
            K hAbove hBelow hFree p)

#check (AlgebraicGeometry.ChernClass.Derived.existsUniqueDerivedCharacter :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E)),
    ∃! chE : (p : ℕ) →
        TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ π p) ℚ,
      ∀ {Y : Scheme.{u}} (f : Y ⟶ X) [IsEnvelope f]
        (K : CochainComplex Y.Modules ℤ)
        (hRep : IsIsomorphic (DerivedCategory.Q.obj K)
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
        (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
        (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
        (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (p : ℕ),
        Complex.characterRestriction δ π f p (chE p) =
          Complex.character δ (f ≫ π) (classes.reanchor (Over.mk (f ≫ π)))
            K hAbove hBelow hFree p)

#check (AlgebraicGeometry.ChernClass.Derived.existsUniqueDerivedNewtonClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E)),
    ∃! PE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p,
      ∀ {Y : Scheme.{u}} (f : Y ⟶ X) [IsEnvelope f]
        (K : CochainComplex Y.Modules ℤ)
        (hRep : IsIsomorphic (DerivedCategory.Q.obj K)
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
        (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
        (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
        (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (p : ℕ),
        ChowCohomology.restrictDegree δ
            (Over.homMk f : Over.mk (f ≫ π) ⟶ Over.mk π) (p : ℤ) (PE p) =
          Complex.newtonClass δ (f ≫ π) (classes.reanchor (Over.mk (f ≫ π)))
            K hAbove hBelow hFree p)

#check (AlgebraicGeometry.ChernClass.Derived.defined :
    ∀ (X : Scheme.{u}),
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))

#check (AlgebraicGeometry.ChernClass.Derived.IsDefined :
    ∀ {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace),
    Prop)

#check (AlgebraicGeometry.ChernClass.Derived.isDefined_iff :
    ∀ {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace),
    IsDefined E ↔
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E))

#check (AlgebraicGeometry.ChernClass.Derived.IsDefined.ofEnvelope :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsEnvelope f]
    {E : RingedSpace.ModuleDerived X.toRingedSpace}
    (hRep : RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((RingedSpace.modulePullbackDerived f.toShHom).obj E)),
    IsDefined E)

#check (AlgebraicGeometry.ChernClass.Derived.defined_isClosedUnderIsomorphisms :
    ∀ (X : Scheme.{u}),
    (defined X).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.ChernClass.Derived.IsTotalClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (cE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p),
    Prop)

#check (AlgebraicGeometry.ChernClass.Derived.IsCharacter :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (chE : (p : ℕ) → TensorProduct ℤ
      (ChowCohomology.Nonnegative.degree δ π p) ℚ),
    Prop)

#check (AlgebraicGeometry.ChernClass.Derived.IsNewtonClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (PE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p),
    Prop)

#check (AlgebraicGeometry.ChernClass.Derived.totalClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E),
    (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)

#check (AlgebraicGeometry.ChernClass.Derived.totalClass_spec :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E),
    IsTotalClass δ π classes E (totalClass δ π classes E hPerfect hDefined))

#check (AlgebraicGeometry.ChernClass.Derived.totalClass_unique :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (cE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)
    (hcE : IsTotalClass δ π classes E cE),
    cE = totalClass δ π classes E hPerfect hDefined)

#check (AlgebraicGeometry.ChernClass.Derived.character :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E),
    (p : ℕ) → TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ π p) ℚ)

#check (AlgebraicGeometry.ChernClass.Derived.character_spec :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E),
    IsCharacter δ π classes E (character δ π classes E hPerfect hDefined))

#check (AlgebraicGeometry.ChernClass.Derived.character_unique :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (chE : (p : ℕ) → TensorProduct ℤ
      (ChowCohomology.Nonnegative.degree δ π p) ℚ)
    (hchE : IsCharacter δ π classes E chE),
    chE = character δ π classes E hPerfect hDefined)

#check (AlgebraicGeometry.ChernClass.Derived.newtonClass :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E),
    (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)

#check (AlgebraicGeometry.ChernClass.Derived.newtonClass_spec :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E),
    IsNewtonClass δ π classes E (newtonClass δ π classes E hPerfect hDefined))

#check (AlgebraicGeometry.ChernClass.Derived.newtonClass_unique :
    ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (PE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)
    (hPE : IsNewtonClass δ π classes E PE),
    PE = newtonClass δ π classes E hPerfect hDefined)

end AlgebraicGeometry.ChernClass.Derived
