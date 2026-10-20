/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ChernClass.Modification
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape

universe u v

/- Lemma 42.46.5: a perfect derived module whose Chern classes are defined acquires,
after any integral locally finite type base change and one modification, a bounded
constant-rank finite locally free representative computing every restricted Chern class. -/
@[stacks 0GUF]
#check (AlgebraicGeometry.ChernClass.existsModification :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
    (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.left.toRingedSpace)
    (hE : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect E)
    (W : Over S) [AlgebraicGeometry.IsIntegral W.left] (g : W ⟶ X)
    [AlgebraicGeometry.LocallyOfFiniteType g.left]
    (A : Over S → ℕ → Type v)
    (restrict : ∀ {Y Z : Over S}, (Y ⟶ Z) → ∀ i, A Z i → A Y i)
    (complexChernClass :
      ∀ (Y : Over S), CochainComplex Y.left.Modules ℤ → ∀ i, A Y i)
    (cE : ∀ i, A X i)
    (hDefined :
      ∃ (Y : Over S) (f : Y ⟶ X),
        AlgebraicGeometry.IsEnvelope f.left ∧
          AlgebraicGeometry.RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
            ((AlgebraicGeometry.RingedSpace.modulePullbackDerived f.left.toShHom).obj E))
    (hChernClass :
      ∀ {Y : Over S} (f : Y ⟶ X) (Q : CochainComplex Y.left.Modules ℤ),
        AlgebraicGeometry.IsEnvelope f.left →
          IsIsomorphic (DerivedCategory.Q.obj Q)
            ((AlgebraicGeometry.RingedSpace.modulePullbackDerived f.left.toShHom).obj E) →
          AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedAbove Q →
          AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyBoundedBelow Q →
          (∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree (Q.X n)) →
          ∀ i, restrict f i (cE i) = complexChernClass Y Q i)
    (restrict_comp :
      ∀ {Y Z T : Over S} (f : Y ⟶ Z) (g : Z ⟶ T) (i) (c : A T i),
        restrict (f ≫ g) i c = restrict f i (restrict g i c))
    (complexChernClass_pullback :
      ∀ {Y Z : Over S} (f : Y ⟶ Z) (Q : CochainComplex Z.left.Modules ℤ) (i),
        restrict f i (complexChernClass Z Q i) =
          complexChernClass Y
            (((AlgebraicGeometry.Scheme.Modules.pullback f.left).mapHomologicalComplex
              (up ℤ)).obj Q) i),
    ∃ (W' : Over S) (b : W' ⟶ W) (Q : CochainComplex W'.left.Modules ℤ)
      (r : ℤ → ℕ),
      AlgebraicGeometry.IsModification b.left ∧
        IsIsomorphic (DerivedCategory.Q.obj Q)
          ((AlgebraicGeometry.RingedSpace.modulePullbackDerived
            (b ≫ g).left.toShHom).obj E) ∧
        CochainComplex.bounded W'.left.Modules Q ∧
        (∀ n, AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank (r n) (Q.X n)) ∧
        ∀ i, restrict (b ≫ g) i (cE i) = complexChernClass W' Q i)
