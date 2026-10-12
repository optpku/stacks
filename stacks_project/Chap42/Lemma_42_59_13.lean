/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import stacks_project.Chap42.Lemma_42_59_12_IntersectionProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.ChowGroup
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Assemble identity-square caps of a homogeneous operational class into a degree-shifting
map on total Chow homology. -/
noncomputable def operationalCapTotal
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (i : ℕ)
    (c : ChowCohomology.degree δ X.hom i) :
    ChowGroup.Total δ X →+ ChowGroup.Total δ X :=
  DirectSum.toAddMonoid fun k ↦
    (DirectSum.of (fun n : ℤ ↦ RelativeChow δ X n) (k - (i : ℤ))).comp
      (c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
        IsPullback.of_id_snd k)

/-- Evaluation of `operationalCapTotal` on a homogeneous class is the identity-square cap
in shifted degree. -/
theorem operationalCapTotal_of
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (i : ℕ)
    (c : ChowCohomology.degree δ X.hom i) (k : ℤ) (α : RelativeChow δ X k) :
    operationalCapTotal δ X i c (DirectSum.of _ k α) =
      DirectSum.of (fun n : ℤ ↦ RelativeChow δ X n) (k - (i : ℤ))
        (c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
          IsPullback.of_id_snd k α) :=
  sorry

/-- Cap of one rational operational component against a rational total Chow class. -/
noncomputable def operationalCapRational
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (i : ℕ)
    (c : TensorProduct ℤ (ChowCohomology.degree δ X.hom i) ℚ)
    (γ : rationalChow δ X) : rationalChow δ X :=
  TensorProduct.liftAddHom
    { toFun := fun c0 ↦
        { toFun := fun q ↦
            smulRationalChow δ X q
              ((operationalCapTotal δ X i c0).toIntLinearMap.rTensor ℚ γ)
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry c

/-- `operationalCapRational` scales the identity-square cap of an integral operational class. -/
theorem operationalCapRational_tmul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (i : ℕ)
    (c : ChowCohomology.degree δ X.hom i) (q : ℚ) (γ : rationalChow δ X) :
    operationalCapRational δ X i (c ⊗ₜ[ℤ] q) γ =
      smulRationalChow δ X q
        ((operationalCapTotal δ X i c).toIntLinearMap.rTensor ℚ γ) :=
  sorry

/-- The Section 42.58 action `ch(α') ∩ -` on an arbitrary rational Chow class, summing Chern
degrees through `chernDegreeBound`. -/
noncomputable def chernAct
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤)
    (α' : TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ)
    (γ : rationalChow δ X) : rationalChow δ X :=
  TensorProduct.liftAddHom
    { toFun := fun a ↦
        { toFun := fun q ↦
            smulRationalChow δ X q
              (∑ i ∈ Finset.range (chernDegreeBound hdim + 1),
                operationalCapRational δ X i
                  (Scheme.VectorBundleK0.chernCharacter δ X.hom classes a i) γ)
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry α'

/-- On a pure tensor, `chernAct` scales the truncated Chern-character cap of the integral class. -/
theorem chernAct_tmul
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (classes : ChernClass.Theory δ X.hom)
    (hdim : topologicalKrullDim X.left < ⊤)
    (a : Scheme.VectorBundleK0 X.left) (q : ℚ) (γ : rationalChow δ X) :
    chernAct δ X classes hdim (a ⊗ₜ[ℤ] q) γ =
      smulRationalChow δ X q
        (∑ i ∈ Finset.range (chernDegreeBound hdim + 1),
          operationalCapRational δ X i
            (Scheme.VectorBundleK0.chernCharacter δ X.hom classes a i) γ) :=
  sorry

/-- Proper pushforward on rational total Chow homology. -/
noncomputable def rationalPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    rationalChow δ X →+ rationalChow δ Y :=
  (LinearMap.rTensor ℚ (ChowGroup.Total.map δ f).toIntLinearMap).toAddMonoidHom

/-- `rationalPushforward` is scalar extension of `ChowGroup.Total.map`. -/
theorem rationalPushforward_def
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] :
    rationalPushforward δ f =
      (LinearMap.rTensor ℚ (ChowGroup.Total.map δ f).toIntLinearMap).toAddMonoidHom :=
  sorry

/-- Lemma 42.59.13 (1): in Situation 42.7.1, a morphism `f : X ⟶ Y` of schemes locally of
finite type over `S` is a local complete intersection morphism when `X` and `Y` are
quasi-compact, regular, have affine diagonal, and have finite dimension. -/
@[stacks 0FFA]
theorem isLocalCompleteIntersection_of_regular_quasiCompact
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    [CompactSpace X.left] [CompactSpace Y.left]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
    (dX dY : ℕ) (hXdim : topologicalKrullDim X.left ≤ dX)
    (hYdim : topologicalKrullDim Y.left ≤ dY) :
    LocallyOfType RingHom.IsLocalCompleteIntersection f.left :=
  sorry

/-- Lemma 42.59.13 (2): in Situation 42.7.1, if moreover a Gysin map exists for `f` and `f` is
proper, then `f_*(α · f^! β) = f_* α · β` in `CH^*(Y) ⊗ ℚ`, where the intersection product is
the Section 42.58 action `ch(α') ∩ -` on `ChowGroup.rationalChow`, `α = ch(α') ∩ [X]` and
`β = ch(β') ∩ [Y]` are `chernCapFundamental`, and `f^!` is `gysinMap`. -/
@[stacks 0FFA]
theorem gysin_projection_formula
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [CompactSpace X.left] [CompactSpace Y.left]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    [IsAffineHom (prod.lift (𝟙 Y.left) (𝟙 Y.left))]
    (f : X ⟶ Y) (hf : HasGysinMap f) [IsProper f.left]
    {P : Over S} [LocallyOfFiniteType P.hom]
    (ι : X ⟶ P) (σ : P ⟶ Y) (hι : IsImmersion ι.left)
    [IsClosedImmersion ι.left] [IsRegularImmersion ι.left] [hσ : Smooth σ.left]
    (hfac : ι ≫ σ = f) (t : ℕ) [Scheme.Hom.RelativeDimension σ.left t] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (Scheme.Hom.conormalSheaf ι.left)]
    (e : Scheme.Modules.dual (Scheme.Hom.normalSheaf ι.left) ≅
      Scheme.Hom.conormalSheaf ι.left)
    (D : ClosedSpecialization δ X.hom P.hom ι.left (Over.w ι)
      (ofNormalSheaf ι.left r e))
    (hXdim : topologicalKrullDim X.left < ⊤)
    (hYdim : topologicalKrullDim Y.left < ⊤)
    (classesX : ChernClass.Theory δ X.hom) (classesY : ChernClass.Theory δ Y.hom)
    (α' : TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ)
    (β' : TensorProduct ℤ (Scheme.VectorBundleK0 Y.left) ℚ) :
    rationalPushforward δ f
        (chernAct δ X classesX hXdim α'
          (gysinMap δ f ι σ hι hfac t r e D
            (chernCapFundamental δ Y classesY hYdim β'))) =
      chernAct δ Y classesY hYdim β'
        (rationalPushforward δ f (chernCapFundamental δ X classesX hXdim α')) :=
  sorry

end AlgebraicGeometry.BivariantClass
