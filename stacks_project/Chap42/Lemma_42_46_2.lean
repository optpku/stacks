module

public import stacks_project.Chap42.Lemma_42_35_6
public import stacks_project.Chap42.Lemma_42_46_1
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass

/-- Lemma 42.46.2 (1): a perfect derived module admitting a locally bounded finite locally free
representative after an envelope has a unique total Chern-class family whose restriction along
every such envelope is the total Chern-class family of every eligible representative. -/
@[stacks 0GUD]
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

/-- Lemma 42.46.2 (2): a perfect derived module admitting a locally bounded finite locally free
representative after an envelope has a unique rational Chern-character family whose restriction
along every such envelope is the Chern-character family of every eligible representative. -/
@[stacks 0GUD]
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

/-- Lemma 42.46.2 (3): a perfect derived module admitting a locally bounded finite locally free
representative after an envelope has a unique integral Newton-class family whose restriction
along every such envelope is the Newton-class family of every eligible representative. -/
@[stacks 0GUD]
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

end AlgebraicGeometry.ChernClass
