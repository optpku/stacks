module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification

@[expose] public section

open CategoryTheory ComplexShape

universe u v

namespace AlgebraicGeometry.ChernClass

/-- A perfect derived module with defined Chern classes acquires, after any integral locally
finite type base change and a modification, a bounded constant-rank finite locally free
representative whose Chern classes are the restrictions of the original classes. -/
theorem existsModification
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (W : Over S) [IsIntegral W.left] (g : W ⟶ X) [LocallyOfFiniteType g.left]
    (A : Over S → ℕ → Type v)
    (restrict : ∀ {Y Z : Over S}, (Y ⟶ Z) → ∀ i, A Z i → A Y i)
    (complexChernClass :
      ∀ (Y : Over S), CochainComplex Y.left.Modules ℤ → ∀ i, A Y i)
    (cE : ∀ i, A X i)
    (hDefined :
      ∃ (Y : Over S) (f : Y ⟶ X),
        IsEnvelope f.left ∧
          RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E))
    (hChernClass :
      ∀ {Y : Over S} (f : Y ⟶ X) (Q : CochainComplex Y.left.Modules ℤ),
        IsEnvelope f.left →
          IsIsomorphic (DerivedCategory.Q.obj Q)
            ((RingedSpace.modulePullbackDerived f.left.toShHom).obj E) →
          RingedSpace.CochainComplex.IsLocallyBoundedAbove Q →
          RingedSpace.CochainComplex.IsLocallyBoundedBelow Q →
          (∀ n, Scheme.Modules.IsFiniteLocallyFree (Q.X n)) →
          ∀ i, restrict f i (cE i) = complexChernClass Y Q i)
    (restrict_comp :
      ∀ {Y Z T : Over S} (f : Y ⟶ Z) (g : Z ⟶ T) (i) (c : A T i),
        restrict (f ≫ g) i c = restrict f i (restrict g i c))
    (complexChernClass_pullback :
      ∀ {Y Z : Over S} (f : Y ⟶ Z) (Q : CochainComplex Z.left.Modules ℤ) (i),
        restrict f i (complexChernClass Z Q i) =
          complexChernClass Y
            (((Scheme.Modules.pullback f.left).mapHomologicalComplex (up ℤ)).obj Q) i) :
    ∃ (W' : Over S) (b : W' ⟶ W) (Q : CochainComplex W'.left.Modules ℤ)
      (r : ℤ → ℕ),
      IsModification b.left ∧
        IsIsomorphic (DerivedCategory.Q.obj Q)
          ((RingedSpace.modulePullbackDerived
            (b ≫ g).left.toShHom).obj E) ∧
        CochainComplex.bounded W'.left.Modules Q ∧
        (∀ n, Scheme.Modules.IsFiniteLocallyFreeOfRank (r n) (Q.X n)) ∧
        ∀ i, restrict (b ≫ g) i (cE i) = complexChernClass W' Q i := sorry

end AlgebraicGeometry.ChernClass
