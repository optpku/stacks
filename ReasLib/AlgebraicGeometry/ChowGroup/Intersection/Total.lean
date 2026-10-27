/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Over
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Graph
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.Components
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Smooth
public import ReasLib.AlgebraicGeometry.ChowGroup.TotalFundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.Rational
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SchemeOverField AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual
open scoped BigOperators TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

namespace Total

/-- The intersection pairing on total Chow homology of a smooth scheme over a field,
obtained from the rank-locus intersection product over the scheme and the canonical
projection of its identity fiber product. -/
noncomputable def intersectionProductOfRankLoci (X : SchemeOverField k) [Smooth X.hom]
    (D : DiagonalSpecializationOfRankLoci X) :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X :=
  let e := (Over.forget _).mapIso (asIso (pullback.fst (𝟙 X) (𝟙 X)))
  (@map _ _ (fun _ ↦ 0) _ _ _ _ _ (pullback.fst (𝟙 X) (𝟙 X))
      (inferInstanceAs (IsProper e.hom))).compHom.comp
    (intersectionProductOverOfRankLoci X (𝟙 X) (𝟙 X) D)

/-- On homogeneous classes, the intersection pairing is the finite sum of diagonal
Gysin caps of their exterior product in degrees `n + m - r`. -/
theorem intersectionProductOfRankLoci_of (X : SchemeOverField k) [Smooth X.hom]
    (D : DiagonalSpecializationOfRankLoci X) {n m : ℤ}
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    intersectionProductOfRankLoci X D (DirectSum.of _ n alpha) (DirectSum.of _ m beta) =
      ∑ r ∈ Finset.range ((n + m).toNat + 1),
        DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) X d) (n + m - r)
          ((diagonalGysinClassOfRankLoci X D r).cap
            (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst (n + m)
            (exteriorProductPairing X X n m alpha beta)) := sorry

/-- The total intersection pairing is independent of the model of deformation to the
normal cone of the diagonal. -/
theorem intersectionProductOfRankLoci_independent (X : SchemeOverField k) [Smooth X.hom]
    (D D' : DiagonalSpecializationOfRankLoci X) :
    intersectionProductOfRankLoci X D = intersectionProductOfRankLoci X D' := sorry

/-- On a smooth scheme of constant relative dimension, the total intersection product is
the exterior product capped with the smooth diagonal class. -/
def smoothIntersectionProductOfDimension (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) [RelativeDimension X.hom d] :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X :=
  (Dedekind.Total.cap (fun _ ↦ 0) (diagonalGysinClassSmooth X d)
    (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst).compHom.comp
      (exteriorProduct X X)

/-- On homogeneous inputs the constant-dimensional total product is the homogeneous
smooth intersection product in degree `n + m - d`. -/
theorem smoothIntersectionProductOfDimension_of (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) [RelativeDimension X.hom d] {n m : ℤ}
    (α : RelativeChow (fun _ ↦ 0) X n) (β : RelativeChow (fun _ ↦ 0) X m) :
    smoothIntersectionProductOfDimension X d (DirectSum.of _ n α) (DirectSum.of _ m β) =
      DirectSum.of (fun t : ℤ ↦ RelativeChow (fun _ ↦ 0) X t) (n + m - d)
        (ChowGroup.smoothIntersectionProduct X d α β) := sorry

/-- Restriction of total Chow homology to a clopen dimension component is degree-zero
flat pullback along its inclusion. -/
def dimensionComponentRestrict (X : SchemeOverField k) [Smooth X.hom] (d : ℕ) :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) (dimensionComponent X d) :=
  Dedekind.Total.cap (fun _ ↦ 0)
    (BivariantClass.flatPullback (fun _ ↦ 0)
      (restrictOpenι X (smoothRelativeDimensionLocus X.hom d)) 0)
    (𝟙 (dimensionComponent X d)) (dimensionComponentι X d) (𝟙 X) IsPullback.of_id_fst

/-- The total smooth intersection product is the sum of the diagonal products on the
clopen dimension components, pushed forward to the original scheme. -/
def smoothIntersectionProduct (X : SchemeOverField k) [Smooth X.hom]
    [CompactSpace X.left] :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X :=
  ∑ n ∈ relativeDimensionDegrees (fun _ ↦ 0) X,
    (((smoothIntersectionProductOfDimension (dimensionComponent X n.toNat) n.toNat).comp
      (dimensionComponentRestrict X n.toNat)).compl₂
        (dimensionComponentRestrict X n.toNat)).compr₂
          (map (fun _ ↦ 0) (dimensionComponentι X n.toNat))

/-- Evaluation of the total smooth product is the finite sum of its dimension-component
products after restriction and proper pushforward. -/
theorem smoothIntersectionProduct_def (X : SchemeOverField k) [Smooth X.hom]
    [CompactSpace X.left] (α β : Total (fun _ ↦ 0) X) :
    smoothIntersectionProduct X α β =
      ∑ n ∈ relativeDimensionDegrees (fun _ ↦ 0) X,
        map (fun _ ↦ 0) (dimensionComponentι X n.toNat)
          (smoothIntersectionProductOfDimension (dimensionComponent X n.toNat) n.toNat
            (dimensionComponentRestrict X n.toNat α)
            (dimensionComponentRestrict X n.toNat β)) := sorry

/-- For a smooth scheme of constant relative dimension, assembly over dimension components
recovers the total diagonal product. -/
theorem smoothIntersectionProduct_ofDimension (X : SchemeOverField k) [Smooth X.hom]
    [CompactSpace X.left] (d : ℕ) [RelativeDimension X.hom d] :
    smoothIntersectionProduct X = smoothIntersectionProductOfDimension X d := sorry

/-- On homogeneous inputs of a constant-dimensional smooth scheme, the assembled total
product is the homogeneous smooth intersection product. -/
theorem smoothIntersectionProduct_of (X : SchemeOverField k) [Smooth X.hom]
    [CompactSpace X.left] (d : ℕ) [RelativeDimension X.hom d] {n m : ℤ}
    (α : RelativeChow (fun _ ↦ 0) X n) (β : RelativeChow (fun _ ↦ 0) X m) :
    smoothIntersectionProduct X (DirectSum.of _ n α) (DirectSum.of _ m β) =
      DirectSum.of (fun t : ℤ ↦ RelativeChow (fun _ ↦ 0) X t) (n + m - d)
        (ChowGroup.smoothIntersectionProduct X d α β) := sorry

/-- The intersection product of total Chow classes on a scheme over a field, obtained by
capping the total exterior product with the canonical Gysin class of the diagonal. -/
noncomputable def intersectionProduct (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X :=
  (Dedekind.Total.cap (fun _ ↦ 0) (diagonalGysinClass X r D)
      (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst).compHom.comp
    (exteriorProduct X X)

/-- The total intersection product is the total cap of the exterior product by the
canonical diagonal Gysin class. -/
theorem intersectionProduct_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha beta : Total (fun _ ↦ 0) X) :
    intersectionProduct X r D alpha beta =
      Dedekind.Total.cap (fun _ ↦ 0) (diagonalGysinClass X r D)
        (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst
        (exteriorProduct X X alpha beta) := rfl

/-- The total intersection product of homogeneous classes is the homogeneous degreewise
product in degree `n + m - r`. -/
theorem intersectionProduct_of (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    intersectionProduct X r D (DirectSum.of _ n alpha) (DirectSum.of _ m beta) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) X d) (n + m - r)
        (ChowGroup.intersectionProduct X r D alpha beta) := sorry


end Total

/-- Rational scalar extension of the integral total smooth intersection product. -/
def smoothIntersectionProductRational (X : SchemeOverField k) [Smooth X.hom]
    [CompactSpace X.left] :
    rationalChow (fun _ ↦ 0) X →+ rationalChow (fun _ ↦ 0) X →+
      rationalChow (fun _ ↦ 0) X :=
  let integral := (addMonoidHomLequivInt ℤ).toLinearMap.comp
    (Total.smoothIntersectionProduct X).toIntLinearMap
  ((addMonoidHomLequivInt ℤ).symm.toLinearMap.comp
    (TensorProduct.map₂ integral (LinearMap.mul ℤ ℚ))).toAddMonoidHom

/-- On two pure tensors, the rational smooth intersection product tensors the integral
product with the product of their rational coefficients. -/
theorem smoothIntersectionProductRational_tmul (X : SchemeOverField k) [Smooth X.hom]
    [CompactSpace X.left] (a b : Total (fun _ ↦ 0) X) (q q' : ℚ) :
    smoothIntersectionProductRational X (a ⊗ₜ[ℤ] q) (b ⊗ₜ[ℤ] q') =
      Total.smoothIntersectionProduct X a b ⊗ₜ[ℤ] (q * q') := sorry

/-- The dimension completion of total Chow homology is its product over the clopen
constant-dimensional components of a smooth scheme. -/
abbrev DimensionCompleted (X : SchemeOverField k) [Smooth X.hom] :=
  ∀ d : ℕ, Total (fun _ ↦ 0) (dimensionComponent X d)

namespace DimensionCompleted

/-- Restricting to all clopen dimension components embeds total Chow homology into its
dimension completion. -/
def embed (X : SchemeOverField k) [Smooth X.hom] :
    Total (fun _ ↦ 0) X →+ DimensionCompleted X where
  toFun a d := Total.dimensionComponentRestrict X d a
  map_zero' := funext fun d ↦ map_zero (Total.dimensionComponentRestrict X d)
  map_add' a b := funext fun d ↦ map_add (Total.dimensionComponentRestrict X d) a b

/-- A total Chow class is determined by its restrictions to all dimension components. -/
theorem embed_injective (X : SchemeOverField k) [Smooth X.hom] :
    Function.Injective (embed X) := sorry

/-- The intersection pairing on the dimension completion is the pointwise integral
intersection pairing on each clopen dimension component. -/
def intersectionProduct (X : SchemeOverField k) [Smooth X.hom]
    (DX : ∀ d, DiagonalSpecializationOfRankLoci (dimensionComponent X d)) :
    DimensionCompleted X →+ DimensionCompleted X →+ DimensionCompleted X where
  toFun a :=
    { toFun := fun b d ↦ Total.intersectionProductOfRankLoci (dimensionComponent X d)
        (DX d) (a d) (b d)
      map_zero' := funext fun d ↦ map_zero
        (Total.intersectionProductOfRankLoci (dimensionComponent X d) (DX d) (a d))
      map_add' := fun b c ↦ funext fun d ↦ map_add
        (Total.intersectionProductOfRankLoci (dimensionComponent X d) (DX d) (a d))
          (b d) (c d) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    funext d
    exact congrArg (fun h ↦ h (b d))
      (map_zero (Total.intersectionProductOfRankLoci (dimensionComponent X d) (DX d)))
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    funext d
    exact congrArg (fun h ↦ h (c d))
      (map_add (Total.intersectionProductOfRankLoci (dimensionComponent X d) (DX d))
        (a d) (b d))

/-- Restriction to the dimension completion preserves the integral intersection product. -/
theorem embed_intersectionProduct (X : SchemeOverField k) [Smooth X.hom]
    (DX : ∀ d, DiagonalSpecializationOfRankLoci (dimensionComponent X d))
    (D : DiagonalSpecializationOfRankLoci X) (alpha beta : Total (fun _ ↦ 0) X) :
    embed X (Total.intersectionProductOfRankLoci X D alpha beta) =
      intersectionProduct X DX (embed X alpha) (embed X beta) := sorry

end DimensionCompleted

/-- The Gysin action of a morphism between arbitrary smooth schemes, evaluated on each
clopen source dimension component through its graph factorization. -/
def gysinMapOfRankLoci {X Y : SchemeOverField k} [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y)
    (D : ∀ d, GraphSpecializationOfRankLoci (dimensionComponentι X d ≫ f)) :
    Total (fun _ ↦ 0) Y →+ DimensionCompleted X where
  toFun a d := gysinMapOfDimension (dimensionComponentι X d ≫ f) (D d) d a
  map_zero' := funext fun d ↦
    map_zero (gysinMapOfDimension (dimensionComponentι X d ≫ f) (D d) d)
  map_add' a b := funext fun d ↦
    map_add (gysinMapOfDimension (dimensionComponentι X d ≫ f) (D d) d) a b

/-- Evaluation of the completed Gysin action at dimension `d` is the finite total
Gysin action for the corresponding source component. -/
theorem gysinMapOfRankLoci_apply {X Y : SchemeOverField k} [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y)
    (D : ∀ d, GraphSpecializationOfRankLoci (dimensionComponentι X d ≫ f))
    (alpha : Total (fun _ ↦ 0) Y) (d : ℕ) :
    gysinMapOfRankLoci f D alpha d =
      gysinMapOfDimension (dimensionComponentι X d ≫ f) (D d) d alpha := rfl

/-- The completed Gysin action is independent of all chosen graph deformation models. -/
theorem gysinMapOfRankLoci_independent {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D D' : ∀ d, GraphSpecializationOfRankLoci (dimensionComponentι X d ≫ f)) :
    gysinMapOfRankLoci f D = gysinMapOfRankLoci f D' := by
  apply AddMonoidHom.ext
  intro alpha
  funext d
  exact congrArg (fun h ↦ h alpha)
    (gysinMapOfDimension_independent (dimensionComponentι X d ≫ f) (D d) (D' d) d)

/-- For a constant-dimensional smooth source and arbitrary smooth target, graph Gysin
pullback preserves the integral intersection product. -/
theorem gysin_intersectionProductOfDimension {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : GraphSpecializationOfRankLoci f) (d : ℕ) [RelativeDimension X.hom d]
    (DX : DiagonalSpecializationOfRankLoci X) (DY : DiagonalSpecializationOfRankLoci Y)
    (alpha beta : Total (fun _ ↦ 0) Y) :
    gysinMapOfDimension f D d (Total.intersectionProductOfRankLoci Y DY alpha beta) =
      Total.intersectionProductOfRankLoci X DX (gysinMapOfDimension f D d alpha)
        (gysinMapOfDimension f D d beta) := sorry

/-- The fixed-degree graph Gysin action preserves the fixed-rank diagonal intersection
product on total Chow homology. -/
theorem gysin_intersectionProduct {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r t rX rY : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t]
    [IsFiniteLocallyFreeOfRank rX (conormalSheaf (diagonal X).left)]
    [IsFiniteLocallyFreeOfRank rY (conormalSheaf (diagonal Y).left)]
    (DX : DiagonalSpecialization X rX) (DY : DiagonalSpecialization Y rY)
    (alpha beta : Total (fun _ ↦ 0) Y) :
    gysinMap f e D r t (Total.intersectionProduct Y rY DY alpha beta) =
      Total.intersectionProduct X rX DX (gysinMap f e D r t alpha)
        (gysinMap f e D r t beta) := sorry


/-- A morphism between arbitrary smooth schemes over a field has a Gysin map, and its
componentwise graph Gysin action preserves integral intersection products. Chosen graph
and diagonal deformation models are explicit; canonical production of these models from
the blowup characterization is a library follow-up. -/
theorem hasGysinMap_and_gysin_intersectionProductOfRankLoci
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : ∀ d, GraphSpecializationOfRankLoci (dimensionComponentι X d ≫ f))
    (DX : ∀ d, DiagonalSpecializationOfRankLoci (dimensionComponent X d))
    (DY : DiagonalSpecializationOfRankLoci Y) (alpha beta : Total (fun _ ↦ 0) Y) :
    BivariantClass.HasGysinMap f ∧
      gysinMapOfRankLoci f D (Total.intersectionProductOfRankLoci Y DY alpha beta) =
        DimensionCompleted.intersectionProduct X DX (gysinMapOfRankLoci f D alpha)
          (gysinMapOfRankLoci f D beta) := by
  refine ⟨BivariantClass.hasGysinMap_of_smooth f, ?_⟩
  funext d
  exact gysin_intersectionProductOfDimension (dimensionComponentι X d ≫ f) (D d) d
    (DX d) DY alpha beta

end AlgebraicGeometry.ChowGroup
