module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChernClass

/- Lemma 42.46.2 (1) -/
@[stacks 0GUD]
#check (AlgebraicGeometry.ChernClass.Derived.existsUniqueDerivedTotalClass :
    {S X : Scheme.{u}} → [UniversallyCatenary S] → (δ : S → ℤ) → [IsDimensionFunction δ] →
    (π : X ⟶ S) → [LocallyOfFiniteType π] → (classes : Theory δ π) →
    (E : RingedSpace.ModuleDerived X.toRingedSpace) →
    RingedSpace.ModuleDerived.IsPerfect E →
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsEnvelope f ∧
        RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) →
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

/- Lemma 42.46.2 (2) -/
@[stacks 0GUD]
#check (AlgebraicGeometry.ChernClass.Derived.existsUniqueDerivedCharacter :
    {S X : Scheme.{u}} → [UniversallyCatenary S] → (δ : S → ℤ) → [IsDimensionFunction δ] →
    (π : X ⟶ S) → [LocallyOfFiniteType π] → (classes : Theory δ π) →
    (E : RingedSpace.ModuleDerived X.toRingedSpace) →
    RingedSpace.ModuleDerived.IsPerfect E →
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsEnvelope f ∧
        RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) →
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

/- Lemma 42.46.2 (3) -/
@[stacks 0GUD]
#check (AlgebraicGeometry.ChernClass.Derived.existsUniqueDerivedNewtonClass :
    {S X : Scheme.{u}} → [UniversallyCatenary S] → (δ : S → ℤ) → [IsDimensionFunction δ] →
    (π : X ⟶ S) → [LocallyOfFiniteType π] → (classes : Theory δ π) →
    (E : RingedSpace.ModuleDerived X.toRingedSpace) →
    RingedSpace.ModuleDerived.IsPerfect E →
    (∃ (Y : Scheme.{u}) (f : Y ⟶ X),
      IsEnvelope f ∧
        RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
          ((RingedSpace.modulePullbackDerived f.toShHom).obj E)) →
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

end AlgebraicGeometry.ChernClass
