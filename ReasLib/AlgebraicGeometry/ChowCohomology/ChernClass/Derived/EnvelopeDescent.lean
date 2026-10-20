/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Complex
public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps
public import ReasLib.AlgebraicGeometry.BivariantClass.Envelope
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope.Composition

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- A perfect derived module with an envelope model determines a unique total Chern-class family
whose restriction to every envelope model is the total Chern-class family of that model. -/
theorem existsUniqueDerivedTotalClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) :
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
            K hAbove hBelow hFree p := sorry

/-- A perfect derived module with an envelope model determines a unique rational Chern-character
family whose restriction to every envelope model is the character of that model. -/
theorem existsUniqueDerivedCharacter
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) :
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
            K hAbove hBelow hFree p := sorry

/-- A perfect derived module with an envelope model determines a unique Newton-class family whose
restriction to every envelope model is the Newton-class family of that model. -/
theorem existsUniqueDerivedNewtonClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E)
    (hDefined :
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) :
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
            K hAbove hBelow hFree p := sorry

/-- The property that a derived module acquires a locally bounded, termwise finite locally free
representative after pullback along an envelope. -/
def defined (X : Scheme.{u}) :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  fun E ↦ ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
    IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj E)

/-- A derived module has defined Chern classes if its pullback along some envelope admits a
locally bounded, termwise finite locally free representative. -/
abbrev IsDefined {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace) : Prop :=
  defined X E

/-- Definedness expands to the existence of an envelope on which the derived pullback has a
locally bounded, termwise finite locally free representative. -/
theorem isDefined_iff {X : Scheme.{u}}
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsDefined E ↔
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X),
        IsEnvelope f ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.toShHom).obj E) := sorry

namespace IsDefined

/-- An explicit envelope and a suitable representative after pullback establish definedness. -/
theorem ofEnvelope {X Y : Scheme.{u}} (f : Y ⟶ X) [IsEnvelope f]
    {E : RingedSpace.ModuleDerived X.toRingedSpace}
    (hRep : RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
      ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) :
    IsDefined E := sorry

end IsDefined

/-- Definedness of derived Chern classes is invariant under isomorphisms of derived modules. -/
instance defined_isClosedUnderIsomorphisms (X : Scheme.{u}) :
    (defined X).IsClosedUnderIsomorphisms := sorry

/-- The descent specification for an integral total Chern-class family of a derived module. -/
def IsTotalClass {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (cE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p) : Prop :=
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
          K hAbove hBelow hFree p

/-- The descent specification for a rational Chern-character family of a derived module. -/
def IsCharacter {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (chE : (p : ℕ) → TensorProduct ℤ
      (ChowCohomology.Nonnegative.degree δ π p) ℚ) : Prop :=
  ∀ {Y : Scheme.{u}} (f : Y ⟶ X) [IsEnvelope f]
    (K : CochainComplex Y.Modules ℤ)
    (hRep : IsIsomorphic (DerivedCategory.Q.obj K)
      ((RingedSpace.modulePullbackDerived f.toShHom).obj E))
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (p : ℕ),
      Complex.characterRestriction δ π f p (chE p) =
        Complex.character δ (f ≫ π) (classes.reanchor (Over.mk (f ≫ π)))
          K hAbove hBelow hFree p

/-- The descent specification for an integral Newton-class family of a derived module. -/
def IsNewtonClass {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (PE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p) : Prop :=
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
          K hAbove hBelow hFree p

/-- The total Chern-class family constructed by cap descent along the fixed family of all
envelope models. -/
noncomputable def totalClass {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p :=
  fun p => LocalizedChern.EnvelopeCaps.derivedClass δ (X := Over.mk π)
    classes E hPerfect hDefined true p

/-- The selected total Chern-class family satisfies its envelope-descent specification. -/
theorem totalClass_spec {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    IsTotalClass δ π classes E (totalClass δ π classes E hPerfect hDefined) := sorry

/-- A total Chern-class family satisfying descent is the selected family. -/
theorem totalClass_unique {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (cE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)
    (hcE : IsTotalClass δ π classes E cE) :
    cE = totalClass δ π classes E hPerfect hDefined := sorry

/-- The Chern-character family whose degree-`p` component is the descended Newton class
tensored with the inverse factorial `(p.factorial : ℚ)⁻¹`. -/
noncomputable def character {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    (p : ℕ) → TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ π p) ℚ :=
  fun p => TensorProduct.tmul ℤ
    (LocalizedChern.EnvelopeCaps.derivedClass δ (X := Over.mk π)
      classes E hPerfect hDefined false p) ((p.factorial : ℚ)⁻¹)

/-- The selected Chern-character family satisfies its envelope-descent specification. -/
theorem character_spec {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    IsCharacter δ π classes E (character δ π classes E hPerfect hDefined) := sorry

/-- A Chern-character family satisfying descent is the selected family. -/
theorem character_unique {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (chE : (p : ℕ) → TensorProduct ℤ
      (ChowCohomology.Nonnegative.degree δ π p) ℚ)
    (hchE : IsCharacter δ π classes E chE) :
    chE = character δ π classes E hPerfect hDefined := sorry

/-- The Newton-class family constructed by cap descent along the fixed family of all
envelope models. -/
noncomputable def newtonClass {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p :=
  fun p => LocalizedChern.EnvelopeCaps.derivedClass δ (X := Over.mk π)
    classes E hPerfect hDefined false p

/-- The selected Newton-class family satisfies its envelope-descent specification. -/
theorem newtonClass_spec {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E) :
    IsNewtonClass δ π classes E (newtonClass δ π classes E hPerfect hDefined) := sorry

/-- A Newton-class family satisfying descent is the selected family. -/
theorem newtonClass_unique {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (π : X ⟶ S) [LocallyOfFiniteType π]
    (classes : Theory δ π) (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hPerfect : RingedSpace.ModuleDerived.IsPerfect E) (hDefined : IsDefined E)
    (PE : (p : ℕ) → ChowCohomology.Nonnegative.degree δ π p)
    (hPE : IsNewtonClass δ π classes E PE) :
    PE = newtonClass δ π classes E hPerfect hDefined := sorry
end AlgebraicGeometry.ChernClass.Derived
