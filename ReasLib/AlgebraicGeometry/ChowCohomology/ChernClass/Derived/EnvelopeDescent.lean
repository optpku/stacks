/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Complex
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

end AlgebraicGeometry.ChernClass.Derived
