/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Group
public import ReasLib.AlgebraicGeometry.BivariantClass.Composition
public import ReasLib.AlgebraicGeometry.BivariantClass.FlatPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

private theorem smooth_eq_of_cap_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {f : X ⟶ Y} {p : ℤ} {c c' : BivariantClass δ f p}
    (h : (c.cap : CapFamily δ f p) = (c'.cap : CapFamily δ f p)) : c = c' := by
  rcases c with ⟨cap, hproper, hflat, hcartier⟩
  rcases c' with ⟨cap', hproper', hflat', hcartier'⟩
  change @cap = @cap' at h
  cases h
  rfl

/-- Composition with smooth flat pullback, transported to the shifted degree, preserves zero. -/
theorem compSmooth_map_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    Nonnegative.castGrading δ (sub_eq_add_neg p (d : ℤ)).symm
      (comp δ f g (0 : group δ f p) (flatPullback δ g d)) =
        (0 : group δ (f ≫ g) (p - (d : ℤ))) := by
  change comp δ f g (pointwiseZero δ f p) (flatPullback δ g d) =
    pointwiseZero δ (f ≫ g) (p + -(d : ℤ))
  apply smooth_eq_of_cap_eq δ
  funext X' Z' hX' hZ' i fg' h hfinite square k
  apply AddMonoidHom.ext
  intro a
  exact map_zero (RelativeChow.castDegree δ (X := X') (compDegree k p (-(d : ℤ))))

/-- Composition with smooth flat pullback, transported to the shifted degree, preserves addition. -/
theorem compSmooth_map_add
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) (c c' : group δ f p) :
    Nonnegative.castGrading δ (sub_eq_add_neg p (d : ℤ)).symm
      (comp δ f g (c + c') (flatPullback δ g d)) =
        pointwiseAdd δ (f ≫ g) (p - (d : ℤ))
          (Nonnegative.castGrading δ (sub_eq_add_neg p (d : ℤ)).symm
            (comp δ f g c (flatPullback δ g d)))
          (Nonnegative.castGrading δ (sub_eq_add_neg p (d : ℤ)).symm
            (comp δ f g c' (flatPullback δ g d))) := by
  change comp δ f g (pointwiseAdd δ f p c c') (flatPullback δ g d) =
    pointwiseAdd δ (f ≫ g) (p + -(d : ℤ))
      (comp δ f g c (flatPullback δ g d)) (comp δ f g c' (flatPullback δ g d))
  apply smooth_eq_of_cap_eq δ
  funext X' Z' hX' hZ' i fg' h hfinite square k
  apply AddMonoidHom.ext
  intro a
  exact map_add (RelativeChow.castDegree δ (X := X') (compDegree k p (-(d : ℤ)))) _ _

/-- Composition with the smooth flat-pullback class shifts homogeneous degree by `-d`. -/
def compSmooth
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    group δ f p →+ group δ (f ≫ g) (p - (d : ℤ)) where
  toFun c := Nonnegative.castGrading δ (sub_eq_add_neg p (d : ℤ)).symm
    (comp δ f g c (flatPullback δ g d))
  map_zero' := compSmooth_map_zero δ f g d p
  map_add' := compSmooth_map_add δ f g d p

/-- Composition with the smooth flat-pullback class is bijective in every homogeneous degree. -/
theorem compSmooth_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    Function.Bijective (compSmooth δ f g d p) := sorry

/-- The inverse function to composition with the smooth flat-pullback class. -/
def compSmoothInv
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    group δ (f ≫ g) (p - (d : ℤ)) → group δ f p :=
  Function.invFun (compSmooth δ f g d p)

/-- The inverse to smooth composition recovers each original bivariant class. -/
theorem compSmooth_leftInverse
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    Function.LeftInverse (compSmoothInv δ f g d p) (compSmooth δ f g d p) := by
  exact Function.leftInverse_invFun (compSmooth_bijective δ f g d p).injective

/-- Smooth composition recovers each class from its inverse image. -/
theorem compSmooth_rightInverse
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    Function.RightInverse (compSmoothInv δ f g d p) (compSmooth δ f g d p) := by
  exact Function.rightInverse_invFun (compSmooth_bijective δ f g d p).surjective

/-- Smooth composition identifies homogeneous bivariant groups with the relative-dimension shift. -/
def compSmoothEquiv
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) :
    group δ f p ≃+ group δ (f ≫ g) (p - (d : ℤ)) where
  toFun := compSmooth δ f g d p
  invFun := compSmoothInv δ f g d p
  left_inv := compSmooth_leftInverse δ f g d p
  right_inv := compSmooth_rightInverse δ f g d p
  map_add' := (compSmooth δ f g d p).map_add

/-- The smooth-composition equivalence applies by composition and grading transport. -/
theorem compSmoothEquiv_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ) (c : group δ f p) :
    compSmoothEquiv δ f g d p c =
      Nonnegative.castGrading δ (sub_eq_add_neg p (d : ℤ)).symm
        (comp δ f g c (flatPullback δ g d)) := rfl

/-- The inverse smooth-composition equivalence applies as the specified inverse function. -/
theorem compSmoothEquiv_symm_eq
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ)
    (c' : group δ (f ≫ g) (p - (d : ℤ))) :
    (compSmoothEquiv δ f g d p).symm c' = compSmoothInv δ f g d p c' := rfl

end AlgebraicGeometry.BivariantClass
