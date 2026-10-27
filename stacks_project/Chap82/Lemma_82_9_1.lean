/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.DimensionFormula

/-!
# δ-dimension of inverse images under flat morphisms

The corrected closed-preimage formula, its upper bound and surjective case, and
the component domination and dimension statements for good algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/- Lemma 82.9.1 (1), with the authorized correction: the dimension of a nonempty
closed inverse image equals that of the closure of the intersection of the closed
subset with the morphism's range, plus `r`; the whole-target equality need not hold. -/
@[stacks 0EP5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.closedPreimageDeltaDimension :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (T : Closeds (Points Y)) (hT : Nonempty (T.preimage (Points.continuous_map f))),
    closedSetDeltaDimension pX δ (T.preimage (Points.continuous_map f)) =
      closedSetDeltaDimension pY δ
        (Closeds.closure ((T : Set (Points Y)) ∩ Set.range (Points.map f))) + (r : EInt))

/- Lemma 82.9.1: the upper-bound consequence of the corrected formula. -/
@[stacks 0EP5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.closedPreimageDeltaDimension_le :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (T : Closeds (Points Y)) (hT : Nonempty (T.preimage (Points.continuous_map f))),
    closedSetDeltaDimension pX δ (T.preimage (Points.continuous_map f)) ≤
      closedSetDeltaDimension pY δ T + (r : EInt))

/- Lemma 82.9.1: equality with the entire closed subset under surjectivity. -/
@[stacks 0EP5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.closedPreimageDeltaDimension_of_surjective :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] [AlgebraicGeometry.AlgebraicSpace.Surjective f] (hf : f ≫ pY = pX)
    (T : Closeds (Points Y)) (hT : Nonempty (T.preimage (Points.continuous_map f))),
    closedSetDeltaDimension pX δ (T.preimage (Points.continuous_map f)) =
      closedSetDeltaDimension pY δ T + (r : EInt))

/- Lemma 82.9.1 (2): every inverse-image component dominates the irreducible closed subset. -/
@[stacks 0EP5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.componentOfPreimageMapsTo :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : IrreducibleCloseds (Points Y)) (Z' : IrreducibleCloseds (Points X))
    (hZ' : Z' ∈ closedSetIrreducibleComponents
      (Closeds.preimage ⟨Z.carrier, Z.isClosed⟩ (Points.continuous_map f))),
    IrreducibleCloseds.map (Points.map f) (Points.continuous_map f) Z' = Z)

/- Lemma 82.9.1 (3): every inverse-image component has `δ`-dimension shifted by `r`. -/
@[stacks 0EP5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.componentOfPreimageDeltaDimension :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : IrreducibleCloseds (Points Y)) (Z' : IrreducibleCloseds (Points X))
    (hZ' : Z' ∈ closedSetIrreducibleComponents
      (Closeds.preimage ⟨Z.carrier, Z.isClosed⟩ (Points.continuous_map f))),
    deltaDimension pX δ Z' = deltaDimension pY δ Z + (r : ℤ))

/- Lemma 82.9.1: an integral closed component admits a dominant morphism over `f`. -/
@[stacks 0EP5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.componentOfInverseImage_dominant :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : ClosedSubspace Y) [IsIntegral Z.X] (Z' : ClosedSubspace X)
    [IsIntegral Z'.X]
    (hZ' : ClosedSubspace.irreducibleClosed Z' ∈
      closedSetIrreducibleComponents
        (Closeds.preimage ⟨Z.pointsSet, Z.isClosed_pointsSet⟩
          (Points.continuous_map f))),
    ∃ g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι ≫ f ∧ Dominant g)

/- Lemma 82.9.1: the dimension shift for integral closed subspaces. -/
@[stacks 0EP5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.componentOfInverseImage_deltaDimension :
    ∀ {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (f : X ⟶ Y) (r : ℕ)
    [Flat f] [RelativeDimension f r] (hf : f ≫ pY = pX)
    (Z : ClosedSubspace Y) [IsIntegral Z.X] (Z' : ClosedSubspace X)
    [IsIntegral Z'.X]
    (hZ' : ClosedSubspace.irreducibleClosed Z' ∈
      closedSetIrreducibleComponents
        (Closeds.preimage ⟨Z.pointsSet, Z.isClosed_pointsSet⟩
          (Points.continuous_map f))),
    deltaDimension pX δ (ClosedSubspace.irreducibleClosed Z') =
      deltaDimension pY δ (ClosedSubspace.irreducibleClosed Z) + (r : ℤ))

end AlgebraicGeometry.AlgebraicSpace.Hom
