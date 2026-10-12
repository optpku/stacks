/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType

/-!
# Dimension formulas for flat morphisms

This file records dimension formulas for inverse images under flat morphisms of constant
relative dimension.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom.DimensionFormula

/-- Every irreducible component of the inverse image of an irreducible closed subset under a
flat morphism of constant relative dimension dominates that subset. -/
theorem componentOfPreimageMapsTo
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [RelativeDimension f.left r]
    (Z : IrreducibleCloseds Y.left) (Z' : IrreducibleCloseds X.left)
    (hZ' : Maximal (fun W : IrreducibleCloseds X.left ↦
      (W : Set X.left) ⊆ f.left ⁻¹' (Z : Set Y.left)) Z') :
    IrreducibleCloseds.map f.left f.left.continuous Z' = Z := sorry

/-- Every irreducible component of the inverse image of an irreducible closed subset under a
flat morphism of relative dimension `r` has `δ`-dimension shifted by `r`. -/
theorem componentOfPreimageDeltaDimension
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [RelativeDimension f.left r]
    (Z : IrreducibleCloseds Y.left) (Z' : IrreducibleCloseds X.left)
    (hZ' : Maximal (fun W : IrreducibleCloseds X.left ↦
      (W : Set X.left) ⊆ f.left ⁻¹' (Z : Set Y.left)) Z') :
    X.hom.deltaDimension δ Z' = Y.hom.deltaDimension δ Z + (r : ℤ) := sorry

/-- A flat morphism of relative dimension `r` shifts the `δ`-dimension of every closed subset
with nonempty inverse image by `r`. -/
theorem closedPreimageDeltaDimension
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [RelativeDimension f.left r]
    (Z : Closeds Y.left) (hZ : Nonempty (Z.preimage f.left.continuous)) :
    X.hom.closedSubschemeDeltaDimension δ
        (IdealSheafData.vanishingIdeal (Z.preimage f.left.continuous)) =
      Y.hom.closedSubschemeDeltaDimension δ (IdealSheafData.vanishingIdeal Z) +
        (r : EInt) := sorry

end AlgebraicGeometry.Scheme.Hom.DimensionFormula
