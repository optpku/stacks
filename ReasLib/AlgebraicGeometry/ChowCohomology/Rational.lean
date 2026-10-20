module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

open CategoryTheory
open scoped DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology.Nonnegative

/-- Embed a rationalized homogeneous Chow-cohomology component into the rationalized
total nonnegative Chow-cohomology ring. -/
noncomputable def rationalHomogeneous {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f] (n : ℕ) :
    TensorProduct ℤ (degree δ f n) ℚ →ₗ[ℤ] TensorProduct ℤ (ring δ f) ℚ :=
  TensorProduct.map (DirectSum.lof ℤ ℕ (degree δ f) n) LinearMap.id

/-- The rational homogeneous embedding sends a pure tensor to the corresponding
homogeneous Chow class tensored with the same rational scalar. -/
theorem rationalHomogeneous_tmul {S X : Scheme.{u}} (δ : S → ℤ) (f : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType f]
    (n : ℕ) (a : degree δ f n) (q : ℚ) :
    rationalHomogeneous δ f n (a ⊗ₜ[ℤ] q) =
      ChernClass.homogeneous δ f n a ⊗ₜ[ℤ] q := sorry

/-- Project a rationalized total nonnegative Chow-cohomology class to its
degree-`i` component. -/
noncomputable def rationalComponent
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p] (i : ℕ) :
    TensorProduct ℤ (ring δ p) ℚ →ₗ[ℤ] TensorProduct ℤ (degree δ p i) ℚ :=
  TensorProduct.map (DirectSum.component ℤ ℕ (degree δ p) i)
    (LinearMap.id : ℚ →ₗ[ℤ] ℚ)

/-- Projecting a rational homogeneous class back to its degree returns that class. -/
theorem rationalComponent_rationalHomogeneous
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (i : ℕ) (x : TensorProduct ℤ (degree δ p i) ℚ) :
    rationalComponent δ p i (rationalHomogeneous δ p i x) = x := sorry

end AlgebraicGeometry.ChowCohomology.Nonnegative
