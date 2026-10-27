/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.BivariantClass.Group
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

section DimensionedBase

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]

/-- Capping an identity bivariant class with the degree-`d` fundamental Chow class. -/
def capFundamental (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c : group δ (𝟙 X) p) : RelativeChow δ X (d - p) :=
  c.cap (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_fst d
    (RelativeChow.fundamentalClass δ X d)

/-- Fundamental-class cap is the identity-square cap of the fundamental cycle class. -/
theorem capFundamental_apply (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c : group δ (𝟙 X) p) :
    capFundamental δ X d p c =
      c.cap (𝟙 X) (𝟙 X) (𝟙 X) IsPullback.of_id_fst d
        (RelativeChow.fundamentalClass δ X d) := sorry

/-- Fundamental-class cap sends the zero bivariant class to zero. -/
theorem capFundamental_zero (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ) :
    capFundamental δ X d p (0 : group δ (𝟙 X) p) = 0 := sorry

/-- Fundamental-class cap preserves addition of bivariant classes. -/
theorem capFundamental_add (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c c' : group δ (𝟙 X) p) :
    capFundamental δ X d p (c + c') =
      capFundamental δ X d p c + capFundamental δ X d p c' := sorry

/-- Fundamental-class cap as an additive homomorphism. -/
def capFundamentalAddHom (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ) :
    group δ (𝟙 X) p →+ RelativeChow δ X (d - p) where
  toFun := capFundamental δ X d p
  map_zero' := capFundamental_zero δ X d p
  map_add' := capFundamental_add δ X d p

/-- The additive fundamental-class cap map evaluates by identity-square cap. -/
theorem capFundamentalAddHom_apply (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c : group δ (𝟙 X) p) :
    capFundamentalAddHom δ X d p c = capFundamental δ X d p c := sorry

/-- Composition of homogeneous identity bivariant classes, transported to the identity map. -/
def identityComp (X : Over S) [LocallyOfFiniteType X.hom] {p q : ℤ}
    (c : group δ (𝟙 X) p) (c' : group δ (𝟙 X) q) : group δ (𝟙 X) (p + q) :=
  Category.id_comp (𝟙 X) ▸ comp δ (𝟙 X) (𝟙 X) c c'

/-- Identity composition is bivariant composition with the categorical identity transport. -/
theorem identityComp_def (X : Over S) [LocallyOfFiniteType X.hom] {p q : ℤ}
    (c : group δ (𝟙 X) p) (c' : group δ (𝟙 X) q) :
    identityComp δ X c c' = Category.id_comp (𝟙 X) ▸ comp δ (𝟙 X) (𝟙 X) c c' := sorry

end DimensionedBase

section OverField

variable {k : Type u} [Field k]

/-- Fundamental-class cap is bijective for a smooth scheme of constant dimension over a field. -/
theorem capFundamental_bijective (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ) :
    Function.Bijective (capFundamental (fun _ ↦ 0) X (d : ℤ) p) := sorry

/-- The inverse to fundamental-class cap on a smooth constant-dimensional scheme. -/
def capFundamentalInv (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ) :
    RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p) → group (fun _ ↦ 0) (𝟙 X) p :=
  Function.invFun (capFundamental (fun _ ↦ 0) X (d : ℤ) p)

/-- The inverse to fundamental-class cap recovers each bivariant class. -/
theorem capFundamentalInv_leftInverse (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ) :
    Function.LeftInverse (capFundamentalInv X d p)
      (capFundamental (fun _ ↦ 0) X (d : ℤ) p) := sorry

/-- Fundamental-class cap recovers each Chow class from its inverse image. -/
theorem capFundamentalInv_rightInverse (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ) :
    Function.RightInverse (capFundamentalInv X d p)
      (capFundamental (fun _ ↦ 0) X (d : ℤ) p) := sorry

/-- Fundamental-class cap identifies operational Chow cohomology with complementary Chow
homology on a smooth scheme of constant dimension over a field. -/
def capFundamentalEquiv (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ) :
    group (fun _ ↦ 0) (𝟙 X) p ≃+ RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p) where
  toFun := capFundamental (fun _ ↦ 0) X (d : ℤ) p
  invFun := capFundamentalInv X d p
  left_inv := capFundamentalInv_leftInverse X d p
  right_inv := capFundamentalInv_rightInverse X d p
  map_add' := (capFundamentalAddHom (fun _ ↦ 0) X (d : ℤ) p).map_add

/-- The forward duality map is cap with the fundamental class. -/
theorem capFundamentalEquiv_apply (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ) (c : group (fun _ ↦ 0) (𝟙 X) p) :
    capFundamentalEquiv X d p c = capFundamental (fun _ ↦ 0) X (d : ℤ) p c := sorry

/-- The inverse duality map is the specified inverse to fundamental-class cap. -/
theorem capFundamentalEquiv_symm_apply (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ)
    (alpha : RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p)) :
    (capFundamentalEquiv X d p).symm alpha = capFundamentalInv X d p alpha := sorry

/-- The grading identity for the intersection of two complementary-dimensional caps. -/
theorem capFundamental_comp_degree (d : ℕ) (p q : ℤ) :
    (d : ℤ) - p + ((d : ℤ) - q) - d = (d : ℤ) - (p + q) := sorry

/-- The grading identity for the action of a complementary-dimensional class. -/
theorem capFundamentalEquiv_symm_cap_degree (d : ℕ) (p n : ℤ) :
    (d : ℤ) - p + n - d = n - p := sorry

/-- The inverse duality class acts on every locally finite-type test scheme by intersection
with its defining Chow class. -/
theorem capFundamentalEquiv_symm_cap (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) [RelativeDimension X.hom d] (p : ℤ)
    (alpha : RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p))
    {Y : SchemeOverField k} (fY : Y ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType fY.left]
    (n : ℤ) (beta : RelativeChow (fun _ ↦ 0) Y n) :
    ((capFundamentalEquiv X d p).symm alpha).cap fY (𝟙 Y) fY
        IsPullback.of_id_snd n beta =
      RelativeChow.castDegree (fun _ ↦ 0) (capFundamentalEquiv_symm_cap_degree d p n)
        (ChowGroup.map (fun _ ↦ 0) (pullback (𝟙 X) fY) Y
          (pullback.snd (𝟙 X) fY) ((d : ℤ) - p + n - d)
          (ChowGroup.smoothIntersectionProductOver X (𝟙 X) fY d alpha beta)) := sorry

/-- Fundamental-class cap carries composition of homogeneous operational classes to the
smooth diagonal intersection product, in the same order. -/
theorem capFundamental_comp (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p q : ℤ)
    (c : group (fun _ ↦ 0) (𝟙 X) p) (c' : group (fun _ ↦ 0) (𝟙 X) q) :
    capFundamental (fun _ ↦ 0) X (d : ℤ) (p + q)
        (identityComp (fun _ ↦ 0) X c c') =
      RelativeChow.castDegree (fun _ ↦ 0) (capFundamental_comp_degree d p q)
        (ChowGroup.smoothIntersectionProduct X d
          (capFundamental (fun _ ↦ 0) X (d : ℤ) p c)
          (capFundamental (fun _ ↦ 0) X (d : ℤ) q c')) := sorry

end OverField

end AlgebraicGeometry.BivariantClass
