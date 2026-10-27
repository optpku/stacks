/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Reanchor
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernCharacter
public import ReasLib.AlgebraicGeometry.ChowGroup.Rational
public import ReasLib.AlgebraicGeometry.ChowGroup.TotalFundamental
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- A finite Krull dimension supplies a truncation bound for Chern-character degrees. -/
noncomputable def chernDegreeBound {X : Type u} [TopologicalSpace X]
    (hdim : topologicalKrullDim X < ⊤) : ℕ :=
  (fun _ : topologicalKrullDim X < ⊤ =>
    ENat.toNat (WithBot.unbotD (0 : ℕ∞) (topologicalKrullDim X))) hdim

/-- Cap a homogeneous operational class onto the degree-`n` fundamental class. -/
noncomputable def capOnFundamental {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (p n : ℤ) :
    ChowCohomology.degree δ X.hom p →+ RelativeChow δ X (n - p) where
  toFun c :=
    c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
      IsPullback.of_id_snd n (RelativeChow.fundamentalClass δ (Over.mk X.hom) n)
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation of `capOnFundamental` is the identity-square cap of the fundamental class. -/
theorem capOnFundamental_apply {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (p n : ℤ) (c : ChowCohomology.degree δ X.hom p) :
    capOnFundamental δ X p n c =
      c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
        IsPullback.of_id_snd n
        (RelativeChow.fundamentalClass δ (Over.mk X.hom) n) :=
  rfl

/-- Linear extension of Chern character followed by capping homogeneous components with
the fundamental class into total rational Chow. -/
noncomputable def chernCapFundamentalAdd {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤) :
    Scheme.VectorBundleK0 X.left →+ rationalChow δ X where
  toFun a :=
    ∑ i ∈ Finset.range (chernDegreeBound hdim + 1),
      ∑ n ∈ relativeDimensionDegrees δ X,
        TensorProduct.map
          (DirectSum.lof ℤ ℤ (fun d ↦ RelativeChow δ X d) (n - (i : ℤ)))
          (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
          (TensorProduct.map (capOnFundamental δ X (i : ℤ) n).toIntLinearMap
            (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
            (Scheme.VectorBundleK0.chernCharacter δ X.hom classes a i))
  map_zero' := sorry
  map_add' := sorry

/-- The rational Chern-cap-fundamental map, linearly extending `ch(-) ∩ [X]` over `Q`. -/
noncomputable def chernCapFundamental {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤) :
    TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ →+ rationalChow δ X :=
  let integralChernCap : Scheme.VectorBundleK0 X.left →ₗ[ℤ] rationalChow δ X :=
    @AddMonoidHom.toIntLinearMap (Scheme.VectorBundleK0 X.left) (rationalChow δ X)
      (Scheme.VectorBundleK0.instCommRing X.left).toAddCommGroup inferInstance
      (chernCapFundamentalAdd δ X classes hdim)
  let toLeftRational := (TensorProduct.comm ℤ (Total δ X) ℚ).toLinearMap.comp integralChernCap
  ((TensorProduct.comm ℤ ℚ (Total δ X)).toLinearMap.comp
    (((toLeftRational.liftBaseChange ℚ).restrictScalars ℤ).comp
      (TensorProduct.comm ℤ (Scheme.VectorBundleK0 X.left) ℚ).toLinearMap)).toAddMonoidHom

/-- On a pure tensor, `chernCapFundamental` scales the integral Chern-cap-fundamental map. -/
theorem chernCapFundamental_tmul {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤) (a : Scheme.VectorBundleK0 X.left) (q : ℚ) :
    chernCapFundamental δ X classes hdim (a ⊗ₜ[ℤ] q) =
      smulRationalChow δ X q (chernCapFundamentalAdd δ X classes hdim a) :=
  sorry

/-- The product represented by two rational vector-bundle classes is their product capped with the fundamental class through the Chern character. -/
noncomputable def rationalIntersectionProduct {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤)
    (α β : TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ) : rationalChow δ X :=
  chernCapFundamental δ X classes hdim (α * β)

/-- The rational intersection product is Chern-cap-fundamental of the `K₀ ⊗ Q` product. -/
theorem rationalIntersectionProduct_def {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤)
    (α β : TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ) :
    rationalIntersectionProduct δ X classes hdim α β =
      chernCapFundamental δ X classes hdim (α * β) :=
  rfl

section Regular

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable (X : Over S) [LocallyOfFiniteType X.hom] [CompactSpace X.left]
variable [hRegular : Scheme.Regular X.left]
variable [hAffine : IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
variable (classes : ChernClass.Theory δ X.hom) (hdim : topologicalKrullDim X.left < ⊤)

include hRegular hAffine

/-- Chern character capped with the fundamental class identifies rational vector-bundle
K-theory with rational Chow homology on a quasi-compact regular finite-dimensional scheme
with affine diagonal. -/
theorem chernCapFundamental_bijective :
    Function.Bijective (chernCapFundamental δ X classes hdim) := sorry

/-- The additive Chern-cap equivalence has the Chern-cap map as its forward function and
its set-theoretic inverse as its reverse function. -/
noncomputable def chernCapFundamentalEquiv :
    TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ ≃+ rationalChow δ X where
  toFun := chernCapFundamental δ X classes hdim
  invFun := Function.invFun (chernCapFundamental δ X classes hdim)
  left_inv := Function.leftInverse_invFun (chernCapFundamental_bijective δ X classes hdim).1
  right_inv := Function.rightInverse_invFun (chernCapFundamental_bijective δ X classes hdim).2
  map_add' := (chernCapFundamental δ X classes hdim).map_add

/-- Intersection of rational Chow classes is multiplication in rational vector-bundle K-theory
transported through Chern character capped with the fundamental class. -/
noncomputable def regularIntersectionProduct (α β : rationalChow δ X) : rationalChow δ X :=
  chernCapFundamentalEquiv δ X classes hdim
    ((chernCapFundamentalEquiv δ X classes hdim).symm α *
      (chernCapFundamentalEquiv δ X classes hdim).symm β)

/-- Intersection of Chern-cap images agrees with the product represented by the original
rational vector-bundle classes. -/
theorem regularIntersectionProduct_chernCapFundamental
    (α β : TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ) :
    regularIntersectionProduct δ X classes hdim
      (chernCapFundamental δ X classes hdim α) (chernCapFundamental δ X classes hdim β) =
        rationalIntersectionProduct δ X classes hdim α β := sorry

end Regular

end AlgebraicGeometry.ChowGroup
