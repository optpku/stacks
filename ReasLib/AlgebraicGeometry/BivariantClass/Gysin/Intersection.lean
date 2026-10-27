/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Regular
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Canonical
public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Rational
public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.NormalSheaf
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Commutation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Regular

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

open Scheme.Hom Scheme.Hom.VirtualNormalBundle ChowGroup

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
    (D : ClosedDeformation X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e)) :
    Total δ Y →+ Total δ X :=
  DirectSum.toAddMonoid fun k ↦
    (DirectSum.of (fun d ↦ RelativeChow δ X d) (k - ((r : ℤ) + (-(t : ℤ))))).comp
      ((hfac ▸ BivariantClass.comp δ ι σ
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
    (D : ClosedDeformation X.hom P.hom ι.left (Over.w ι)
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
    (D : ClosedDeformation X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (k : ℤ) (α : RelativeChow δ Y k) (q : ℚ) :
    gysinMap δ f ι σ hι hfac t r e D (DirectSum.of _ k α ⊗ₜ[ℤ] q) =
      DirectSum.of (fun d ↦ RelativeChow δ X d) (k - ((r : ℤ) + (-(t : ℤ))))
          ((hfac ▸ BivariantClass.comp δ ι σ
              (overHom_eq_over ι ▸
                globalClassOfRank δ X.hom P.hom ι.left (Over.w ι)
                  (ofNormalSheaf ι.left r e) D r)
              (flatPullback δ σ t)).cap (𝟙 X) f (𝟙 Y)
            (IsPullback.id_horiz f.left) k α) ⊗ₜ[ℤ] q :=
  sorry

section Regular

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
variable [CompactSpace X.left] [CompactSpace Y.left]
variable [Scheme.Regular X.left] [Scheme.Regular Y.left]
variable [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
variable [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
variable (f : X ⟶ Y) (hf : HasGysinMap f)
variable (hXdim : topologicalKrullDim X.left < ⊤) (hYdim : topologicalKrullDim Y.left < ⊤)
variable (classes : ChernClass.Theory δ Y.hom)

/-- The rational Gysin action between regular finite-dimensional schemes is vector-bundle
pullback transported through the Chern-cap additive equivalences. -/
noncomputable def gysinMapRegular : rationalChow δ Y →+ rationalChow δ X :=
  (chernCapFundamentalEquiv δ X (classes.reanchor X) hXdim).toAddMonoidHom.comp
    ((Scheme.VectorBundleK0.pullbackRational f.left).comp
      (chernCapFundamentalEquiv δ Y classes hYdim).symm.toAddMonoidHom)

include hf in
/-- In every integer degree, the rational Gysin action on a homogeneous Chow class agrees
with the geometric coefficient of any regular-immersion–smooth factorization, allowing
varying normal ranks and smooth relative dimensions. -/
theorem gysinMapRegular_factorizationClassDegree
    {P : Over S} [LocallyOfFiniteType P.hom]
    (i : X ⟶ P) (g : P ⟶ Y) [IsRegularImmersion i.left] [Smooth g.left]
    (hfac : i ≫ g = f)
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf i.left) ≅
      Scheme.Hom.conormalSheaf i.left)
    (D : ClosedDeformation X.hom (i.left.coborderRange.ι ≫ P.hom)
      i.left.liftCoborder
      (by rw [← Category.assoc, i.left.liftCoborder_ι]; exact Over.w i)
      (Gysin.normalBundle i.left e).toCoborder)
    (p k : ℤ) (α : RelativeChow δ Y k) (q : ℚ) :
    TensorProduct.map (DirectSum.component ℤ ℤ (fun d ↦ RelativeChow δ X d) (k - p))
      (LinearMap.id : ℚ →ₗ[ℤ] ℚ)
      (gysinMapRegular δ f hXdim hYdim classes (DirectSum.of _ k α ⊗ₜ[ℤ] q)) =
        (Gysin.factorizationClassDegree δ f i g hfac e D p).cap (𝟙 X) f (𝟙 Y)
          (IsPullback.id_horiz f.left) k α ⊗ₜ[ℤ] q := sorry

/-- Gysin pullback between quasi-compact regular finite-dimensional schemes with affine
diagonal preserves the rational intersection product whenever the Gysin map exists. -/
theorem gysin_rationalIntersectionProduct
    (hf : HasGysinMap f) (α β : rationalChow δ Y) :
    gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom)
      (regularIntersectionProduct δ Y (ChernClass.Theory.canonical δ Y.hom) hYdim α β) =
        regularIntersectionProduct δ X (ChernClass.Theory.canonical δ X.hom) hXdim
          (gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom) α)
          (gysinMapRegular δ f hXdim hYdim (ChernClass.Theory.canonical δ Y.hom) β) := sorry

end Regular

end AlgebraicGeometry.BivariantClass
