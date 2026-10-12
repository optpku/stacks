/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Flat pullback preserves the subgroup of rational boundaries. -/
#check (AlgebraicGeometry.RationalEquivalence.flatPullback_mem_boundaries :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ),
    @AlgebraicGeometry.RationalEquivalence.boundaries Y.left
        (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance k ≤
      (@AlgebraicGeometry.RationalEquivalence.boundaries X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))).comap
        (AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r k))

/- Flat pullback descends from cycle groups to Chow groups. -/
#check (AlgebraicGeometry.ChowGroup.flatPullback :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ),
    @AlgebraicGeometry.ChowGroup Y.left
        (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance k →+
      @AlgebraicGeometry.ChowGroup X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ)))

/- Chow-group flat pullback is computed by flat pullback of cycle representatives. -/
#check (AlgebraicGeometry.ChowGroup.flatPullback_chowClass :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ)
    (α : AlgebraicGeometry.CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k),
    AlgebraicGeometry.ChowGroup.flatPullback δ X Y f r k
        (@AlgebraicGeometry.chowClass Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance k α) =
      @AlgebraicGeometry.chowClass X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k + (r : ℤ))
        (AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r k α))
