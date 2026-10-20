/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The finite pointwise sum of a family of bivariant classes of one degree. -/
def pointwiseSum
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {ι : Type*} (s : Finset ι)
    (c : ι → BivariantClass δ f p) : BivariantClass δ f p :=
  @Finset.sum ι (BivariantClass δ f p)
    (pointwiseAddCommGroup δ f p).toAddCommMonoid s c

/-- Evaluation of a finite pointwise sum by a cap map is the sum of the evaluations. -/
theorem pointwiseSum_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y X' Y' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (p : ℤ) {ι : Type*} (s : Finset ι)
    (c : ι → BivariantClass δ f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (α : RelativeChow δ Y' k) :
    (pointwiseSum δ f p s c).cap i f' g square k α =
      ∑ a ∈ s, (c a).cap i f' g square k α := sorry

end AlgebraicGeometry.BivariantClass
