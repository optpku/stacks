/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import stacks_project.Chap42.Lemma_42_59_12_IntersectionProduct
public import stacks_project.Chap42.Lemma_42_62_1_IntersectionProduct
public import stacks_project.Chap42.Lemma_42_62_2_Comparison
public import stacks_project.Chap42.Lemma_42_62_5_IntersectionProduct

/-!
# Total and rational Section 42.62 self-products

This file packages the identity-square diagonal-Gysin product on total Chow homology
of a scheme over a field, together with its scalar extension to rational Chow.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

namespace Total

/-- The intersection product of total Chow classes on a scheme over a field, obtained by
capping the total exterior product with the canonical Gysin class of the diagonal. -/
noncomputable def intersectionProduct (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X :=
  (BivariantClass.totalCap (fun _ ↦ 0) (diagonalGysinClass X r D)
      (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst).compHom.comp
    (exteriorProduct X X)

/-- The total self-product is the total cap of the exterior product by the canonical
diagonal Gysin class. -/
theorem intersectionProduct_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha beta : Total (fun _ ↦ 0) X) :
    intersectionProduct X r D alpha beta =
      BivariantClass.totalCap (fun _ ↦ 0) (diagonalGysinClass X r D)
        (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst
        (exteriorProduct X X alpha beta) := sorry

/-- The total self-product of homogeneous classes is the homogeneous degreewise product in
degree `n + m - r`. -/
theorem intersectionProduct_of (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth X.hom] {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    intersectionProduct X r D (DirectSum.of _ n alpha) (DirectSum.of _ m beta) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) X d) (n + m - r)
        (ChowGroup.intersectionProduct X r D alpha beta) := sorry

end Total

/-- The Section 42.62 intersection product after tensoring with `ℚ`, obtained by scalar
extension of `Total.intersectionProduct`. -/
noncomputable def intersectionProductRational (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    rationalChow (fun _ ↦ 0) X →+ rationalChow (fun _ ↦ 0) X →+
      rationalChow (fun _ ↦ 0) X :=
  TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun q =>
            (smulRationalChow (fun _ ↦ 0) X q).comp
              (((Total.intersectionProduct X r D a).toIntLinearMap.rTensor ℚ).toAddMonoidHom)
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    sorry

/-- On a pure tensor in the first factor, `intersectionProductRational` scales the
integral total self-product. -/
theorem intersectionProductRational_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (a : Total (fun _ ↦ 0) X) (q : ℚ) (beta : rationalChow (fun _ ↦ 0) X) :
    intersectionProductRational X r D (a ⊗ₜ[ℤ] q) beta =
      smulRationalChow (fun _ ↦ 0) X q
        (((Total.intersectionProduct X r D a).toIntLinearMap.rTensor ℚ).toAddMonoidHom
          beta) := sorry

/-- On pure tensors, `intersectionProductRational` scales the integral total self-product
by the product of the rational coefficients. -/
theorem intersectionProductRational_tmul (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] [Smooth X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (a b : Total (fun _ ↦ 0) X) (q q' : ℚ) :
    intersectionProductRational X r D (a ⊗ₜ[ℤ] q) (b ⊗ₜ[ℤ] q') =
      smulRationalChow (fun _ ↦ 0) X (q * q')
        (Total.intersectionProduct X r D a b ⊗ₜ[ℤ] (1 : ℚ)) := sorry

end AlgebraicGeometry.ChowGroup
