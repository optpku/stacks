/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback

/-!
# Flat pullback along affine-space bundles

This file records surjectivity of flat pullback along a flat morphism that is locally
isomorphic over its target to relative affine space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- If a flat morphism of relative dimension `r` is locally over its target isomorphic to
relative affine `r`-space, then its pullback on Chow groups is surjective. -/
theorem flatPullback_surjective_of_localAffineSpace
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
      Nonempty (Over.mk (f.left ∣_ U) ≅
        Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
    (k : ℤ) : Function.Surjective (flatPullback δ X Y f r k) := sorry

end AlgebraicGeometry.ChowGroup
