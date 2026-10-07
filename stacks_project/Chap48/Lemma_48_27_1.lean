module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Properties

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open scoped ENat DerivedExt

universe u

/- Lemma 48.27.1 (1) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.isDualizing :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    @Scheme.IsDualizingComplex X (LocallyOfFiniteType.isLocallyNoetherian f)
      (properDualizingComplex f).obj)

/- Lemma 48.27.1 (2) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.nonzero_degreeBounds :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (i : ℤ)
    (hi : ¬ IsZero (RingedSpace.ModuleDerived.cohomologySheaf
      (properDualizingComplex f).obj i)),
    -(dimensionIndex f : ℤ) ≤ i ∧ i ≤ 0)

/- Lemma 48.27.1 (3) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_isCoherent :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    (dualizingModule f).IsCoherent)

/- Lemma 48.27.1 (4) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_satisfiesSerreConditionSTwo :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    @Scheme.Modules.satisfiesSerreConditionS X
      (LocallyOfFiniteType.isLocallyNoetherian f) (dualizingModule f)
      (dualizingModule_isCoherent f) 2)

/- Lemma 48.27.1 (5) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_support :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
    RingedSpace.moduleSupport (dualizingModule f) =
      ⋃ Z : irreducibleComponents X,
        ⋃ (_ : topologicalKrullDim Z = topologicalKrullDim X), (Z : Set X))

/- Lemma 48.27.1 (6) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.supportDimension_le :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (hi : i ≤ 0),
    topologicalKrullDim
        (RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
          (properDualizingComplex f).obj i)) ≤
      ((-i).toNat : WithBot ℕ∞))

/- Lemma 48.27.1 (7) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.stalk_nontrivialUpTo_iff_depth :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (x : X) (hx : x ∈ closedPoints X) (i : ℤ) (hi : i ≤ 0),
    (∃ j : ℤ, i ≤ j ∧ j ≤ 0 ∧
      Nontrivial (cohomologyStalk (properDualizingComplex f).obj j x)) ↔
      moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x) ≤
        ((-i).toNat : ℕ∞))

/- Lemma 48.27.1 (8) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.extComparison_bijective :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i : ℤ) (K : DerivedQCoh X),
    Function.Bijective (extComparison f i K))

/- Lemma 48.27.1 (9) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.extComparison_shift :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (i n : ℤ) (K : DerivedQCoh X)
    (g : Ext⁽i⁾(K⟦n⟧, properDualizingComplex f)),
    (cohomologyShiftIso f i n K).hom ≫
        extComparison f (i - n) K (extSourceShift f i n K g) =
      extComparison f i (K⟦n⟧) g)

/- Lemma 48.27.1 (10) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.extComparison_distinguishedBoundary :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (T : Pretriangulated.Triangle (DerivedQCoh X))
    (hT : T ∈ distTriang (DerivedQCoh X)) (i : ℤ)
    (g : Ext⁽i⁾(T.obj₁⟦(1 : ℤ)⟧, properDualizingComplex f)),
    extComparison f i T.obj₃ (T.mor₃ ≫ g) =
      cohomologyOverFieldMap f T.mor₃ (-i) ≫
        extComparison f i (T.obj₁⟦(1 : ℤ)⟧) g)

/- Lemma 48.27.1 (11) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleDualityComparison_bijective :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (F : QCoh X),
    Function.Bijective (moduleDualityComparison f F))

/- Lemma 48.27.1 (12) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.smooth_isomorphic_differentialExteriorShift :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f],
    IsIsomorphic (properDualizingComplex f)
      (Scheme.Hom.differentialExteriorShift f d))

/- Lemma 48.27.1 (13) -/
@[stacks 0FVV] #check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.smooth_dualizingModule_isomorphic_exteriorPower :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (d : ℕ) [SmoothOfRelativeDimension d f],
    IsIsomorphic (dualizingModule f)
      (RingedSpace.ExteriorPower.sheaf (Ω[f.toShHom]) d))
