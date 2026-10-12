/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.BivariantClass.Additive

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Rational bivariant classes are integral bivariant classes tensored with `ℚ` over `ℤ`,
using the explicit pointwise additive structure on integral bivariant classes. -/
abbrev RationalBivariantClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : Type (u + 1) :=
  @TensorProduct ℤ inferInstance ℚ (BivariantClass δ f p)
    inferInstance (pointwiseAddCommGroup δ f p).toAddCommMonoid inferInstance
    (@AddCommGroup.toIntModule (BivariantClass δ f p) (pointwiseAddCommGroup δ f p))

/-- The rational bivariant class obtained by tensoring an integral class with `1 : ℚ`. -/
noncomputable def rationalize
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (c : BivariantClass δ f p) :
    RationalBivariantClass δ f p :=
  @TensorProduct.tmul ℤ inferInstance ℚ (BivariantClass δ f p)
    inferInstance (pointwiseAddCommGroup δ f p).toAddCommMonoid inferInstance
    (@AddCommGroup.toIntModule (BivariantClass δ f p) (pointwiseAddCommGroup δ f p))
    (1 : ℚ) c

end AlgebraicGeometry.BivariantClass
