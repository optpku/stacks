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
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import stacks_project.Chap42.Lemma_42_54_5
public import stacks_project.Chap42.Lemma_42_59_7

/-!
# Rational intersection products from vector-bundle K-theory

This file packages the Section 42.58 product on `CH^* ⊗ Q` for quasi-compact finite-dimensional
schemes, obtained by transporting multiplication on `VectorBundleK0 ⊗ Q` along
`ch(-) ∩ [X]`, together with the identity-square Gysin action on rational Chow.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Rational total Chow homology `CH_*(X) ⊗ Q`, identified with `CH^*(X) ⊗ Q` after
dimension/codimension reindexing on finite-dimensional schemes. -/
abbrev rationalChow {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] : Type u :=
  TensorProduct ℤ (Total δ X) ℚ

/-- `rationalChow` is the tensor product of total relative Chow homology with `Q`. -/
theorem rationalChow_def {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom] :
    rationalChow δ X = TensorProduct ℤ (Total δ X) ℚ :=
  sorry

/-- A finite Krull dimension supplies a truncation bound for Chern-character degrees. -/
noncomputable def chernDegreeBound {X : Type u} [TopologicalSpace X]
    (hdim : topologicalKrullDim X < ⊤) : ℕ :=
  (fun _ : topologicalKrullDim X < ⊤ =>
    ENat.toNat (WithBot.unbotD (0 : ℕ∞) (topologicalKrullDim X))) hdim

/-- Relative dimensions of generic points of a quasi-compact locally finite-type scheme. -/
noncomputable def relativeDimensionDegrees {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] : Finset ℤ :=
  let hNoeth : IsNoetherian X.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  (genericPoints.finite
      (@finite_irreducibleComponents_of_isNoetherian X.left hNoeth)).toFinset.image
    (X.hom.relativeDimensionFunction δ)

/-- Cap a homogeneous operational class onto the degree-`n` fundamental class. -/
noncomputable def capOnFundamental {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (p n : ℤ) :
    ChowCohomology.degree δ X.hom p →+ RelativeChow δ X (n - p) where
  toFun c :=
    c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
      IsPullback.of_id_snd n (Scheme.Hom.VirtualNormalBundle.fundamentalClass_mk δ X.hom n)
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation of `capOnFundamental` is the identity-square cap of the fundamental class. -/
theorem capOnFundamental_apply {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (p n : ℤ) (c : ChowCohomology.degree δ X.hom p) :
    capOnFundamental δ X p n c =
      c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
        IsPullback.of_id_snd n
        (Scheme.Hom.VirtualNormalBundle.fundamentalClass_mk δ X.hom n) :=
  sorry

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

/-- Scale a rational Chow class by a rational number on the `Q` factor. -/
noncomputable def smulRationalChow {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    (q : ℚ) : rationalChow δ X →+ rationalChow δ X :=
  (TensorProduct.map (LinearMap.id : Total δ X →ₗ[ℤ] Total δ X)
      (AddMonoidHom.mulLeft q).toIntLinearMap).toAddMonoidHom

/-- The rational Chern-cap-fundamental map, linearly extending `ch(-) ∩ [X]` over `Q`. -/
noncomputable def chernCapFundamental {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤) :
    TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ →+ rationalChow δ X :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun q => smulRationalChow δ X q (chernCapFundamentalAdd δ X classes hdim a)
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- `chernCapFundamental` scales the integral Chern-cap-fundamental map on the `Q` factor. -/
theorem chernCapFundamental_def {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤)
    (a : Scheme.VectorBundleK0 X.left) (q : ℚ) :
    chernCapFundamental δ X classes hdim (a ⊗ₜ[ℤ] q) =
      smulRationalChow δ X q (chernCapFundamentalAdd δ X classes hdim a) :=
  sorry

/-- On a pure tensor, `chernCapFundamental` scales the integral Chern-cap-fundamental map. -/
theorem chernCapFundamental_tmul {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤) (a : Scheme.VectorBundleK0 X.left) (q : ℚ) :
    chernCapFundamental δ X classes hdim (a ⊗ₜ[ℤ] q) =
      smulRationalChow δ X q (chernCapFundamentalAdd δ X classes hdim a) :=
  sorry

/-- The Section 42.58 intersection product, given by `α · β = ch(α β) ∩ [X]`. -/
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
  sorry

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.Scheme.VectorBundleK0

/-- Rational pullback of vector-bundle `K₀` classes along a scheme morphism. -/
noncomputable def pullbackRational {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TensorProduct ℤ (VectorBundleK0 Y) ℚ →+ TensorProduct ℤ (VectorBundleK0 X) ℚ :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun q => pullback f a ⊗ₜ[ℤ] q
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- Rational pullback on a pure tensor is scalar extension of vector-bundle pullback. -/
theorem pullbackRational_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : VectorBundleK0 Y) (q : ℚ) :
    pullbackRational f (a ⊗ₜ[ℤ] q) = pullback f a ⊗ₜ[ℤ] q :=
  sorry

/-- Rational vector-bundle pullback preserves `K₀ ⊗ Q` multiplication. -/
theorem pullbackRational_map_mul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (α β : TensorProduct ℤ (VectorBundleK0 Y) ℚ) :
    pullbackRational f (α * β) = pullbackRational f α * pullbackRational f β :=
  sorry

end AlgebraicGeometry.Scheme.VectorBundleK0

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom.VirtualNormalBundle ChowGroup

/-- Integral identity-square Gysin action of an LCI factorization on total Chow homology. -/
noncomputable def gysinMapIntegral {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] {X Y : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] {P : Over S}
    [LocallyOfFiniteType P.hom] (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left] [hσ : Smooth σ.left]
    (hfac : ι ≫ σ = f) (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e)) :
    Total δ Y →+ Total δ X :=
  DirectSum.toAddMonoid fun k ↦
    (DirectSum.of (fun d ↦ RelativeChow δ X d) (k - ((r : ℤ) + (-(t : ℤ))))).comp
      ((bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
          (overHom_eq_over ι ▸
            globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
              (ofNormalSheaf ι.left r e) D r)
          (flatPullback δ σ t)).cap (𝟙 X) f (𝟙 Y)
        (IsPullback.id_horiz f.left) k)

/-- The Gysin map `f^!` on rational Chow, obtained by identity-square `totalCap` of the
Gysin class of an LCI factorization, then extended over `Q`. -/
noncomputable def gysinMap {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] {X Y : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] {P : Over S}
    [LocallyOfFiniteType P.hom] (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left] [hσ : Smooth σ.left]
    (hfac : ι ≫ σ = f) (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e)) :
    rationalChow δ Y →+ rationalChow δ X :=
  (gysinMapIntegral δ f ι σ hι hfac t r e D).toIntLinearMap.rTensor ℚ |>.toAddMonoidHom

/-- Evaluation of `gysinMap` is scalar extension of the identity-square Gysin cap. -/
theorem gysinMap_apply {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ)
    [IsDimensionFunction δ] {X Y : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f.left] {P : Over S}
    [LocallyOfFiniteType P.hom] (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left] [hσ : Smooth σ.left]
    (hfac : ι ≫ σ = f) (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (k : ℤ) (α : RelativeChow δ Y k) (q : ℚ) :
    gysinMap δ f ι σ hι hfac t r e D (DirectSum.of _ k α ⊗ₜ[ℤ] q) =
      DirectSum.of (fun d ↦ RelativeChow δ X d) (k - ((r : ℤ) + (-(t : ℤ))))
          ((bivariantGysinClassOfFactorization δ X Y f P ι σ hι hσ hfac
              (overHom_eq_over ι ▸
                globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
                  (ofNormalSheaf ι.left r e) D r)
              (flatPullback δ σ t)).cap (𝟙 X) f (𝟙 Y)
            (IsPullback.id_horiz f.left) k α) ⊗ₜ[ℤ] q :=
  sorry

end AlgebraicGeometry.BivariantClass
