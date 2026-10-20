/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.ChowGroup.Total

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Rational total Chow homology `CH_*(X) ⊗ ℚ`. -/
abbrev rationalChow {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] : Type u :=
  TensorProduct ℤ (Total δ X) ℚ

/-- `rationalChow` is the tensor product of total relative Chow homology with `ℚ`. -/
theorem rationalChow_def {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] :
    rationalChow δ X = TensorProduct ℤ (Total δ X) ℚ :=
  sorry

/-- Scale a rational Chow class by a rational number on the `ℚ` factor. -/
noncomputable def smulRationalChow {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (q : ℚ) : rationalChow δ X →+ rationalChow δ X :=
  (TensorProduct.map (LinearMap.id : Total δ X →ₗ[ℤ] Total δ X)
      (AddMonoidHom.mulLeft q).toIntLinearMap).toAddMonoidHom

/-- `smulRationalChow` scales the `ℚ` factor of a rational Chow class. -/
theorem smulRationalChow_apply {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (q : ℚ) (x : rationalChow δ X) :
    smulRationalChow δ X q x =
      (TensorProduct.map (LinearMap.id : Total δ X →ₗ[ℤ] Total δ X)
          (AddMonoidHom.mulLeft q).toIntLinearMap) x :=
  sorry

/-- Transport `CH_* ⊗ ℚ` along an equality of structure morphisms over `S`. -/
noncomputable def rationalChow.congrHom {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {X : Over S}
    [LocallyOfFiniteType X.hom] (f : X.left ⟶ S)
    [instf : LocallyOfFiniteType f] (h : f = X.hom) :
    @rationalChow S inferInstance δ inferInstance (Over.mk f) instf ≃+ rationalChow δ X where
  toEquiv :=
    Equiv.cast
      (Eq.rec (motive := fun (g : X.left ⟶ S) (e : f = g) =>
          @rationalChow S inferInstance δ inferInstance (Over.mk f) instf =
            @rationalChow S inferInstance δ inferInstance (Over.mk g) (e ▸ instf))
        rfl h : @rationalChow S inferInstance δ inferInstance (Over.mk f) instf = rationalChow δ X)
  map_add' := sorry

/-- Transport along a reflexive equality of structure morphisms is the identity. -/
theorem rationalChow.congrHom_rfl {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] :
    rationalChow.congrHom δ X.hom rfl = AddEquiv.refl (rationalChow δ X) :=
  sorry

end AlgebraicGeometry.ChowGroup
