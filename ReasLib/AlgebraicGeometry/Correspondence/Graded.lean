/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Graded
public import ReasLib.AlgebraicGeometry.Correspondence.Chow
public import ReasLib.AlgebraicGeometry.Correspondence.Graph

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- Smooth projective schemes over a field, viewed as objects of a graded correspondence category. -/
def Graded (k : Type u) [Field k] : Type (u + 1) :=
  {X : SchemeOverField k // Smooth X.hom ∧ Projective X.hom}

namespace Graded

/-- Bundle a supplied smooth projective scheme as a graded correspondence object. -/
def of (scheme : SchemeOverField k) (smooth : Smooth scheme.hom)
    (projective : Projective scheme.hom) : Graded k :=
  ⟨scheme, smooth, projective⟩

/-- The smooth projective scheme underlying a graded correspondence object. -/
def scheme : Graded k → SchemeOverField k := Subtype.val

/-- The underlying scheme of a graded correspondence object is its supplied scheme. -/
theorem scheme_of (X : SchemeOverField k) (h_smooth : Smooth X.hom)
    (h_projective : Projective X.hom) : (Graded.of X h_smooth h_projective).scheme = X := sorry

/-- The underlying scheme of a graded correspondence object is smooth over the field. -/
instance scheme_smooth (X : Graded k) : Smooth X.scheme.hom := sorry

/-- The underlying scheme of a graded correspondence object is projective over the field. -/
instance scheme_projective (X : Graded k) : Projective X.scheme.hom := sorry

/-- The underlying scheme of a graded correspondence object is locally of finite type. -/
instance scheme_locallyOfFiniteType (X : Graded k) : LocallyOfFiniteType X.scheme.hom := sorry

/-- Degree-`r` homogeneous morphisms are rational Chow correspondences of degree `r`. -/
abbrev Homogeneous (X Y : Graded k) (r : ℤ) : Type (u + 1) := Rational X.scheme Y.scheme r

/-- The homogeneous morphism type is the corresponding rational correspondence type. -/
theorem homogeneous_def (X Y : Graded k) (r : ℤ) :
    Homogeneous X Y r = Rational X.scheme Y.scheme r := sorry

/-- The total morphism space is the direct sum of rational correspondences in all degrees. -/
abbrev TotalHom (X Y : Graded k) : Type (u + 1) := ⨁ r : ℤ, Homogeneous X Y r

/-- The total morphism space is definitionally the direct sum of its homogeneous pieces. -/
theorem totalHom_def (X Y : Graded k) : TotalHom X Y = (⨁ r : ℤ, Homogeneous X Y r) := sorry

/-- Include one rational correspondence as a homogeneous total morphism. -/
def homogeneousInclusion (X Y : Graded k) (r : ℤ) :
    Homogeneous X Y r →ₗ[ℚ] TotalHom X Y :=
  DirectSum.lof ℚ ℤ (fun i ↦ Homogeneous X Y i) r

/-- `homogeneousInclusion` is the canonical direct-sum inclusion. -/
theorem homogeneousInclusion_apply (X Y : Graded k) (r : ℤ) (c : Homogeneous X Y r) :
    homogeneousInclusion X Y r c = DirectSum.lof ℚ ℤ (fun i ↦ Homogeneous X Y i) r c := sorry

/-- The degree-zero diagonal correspondence is the rational graph of the identity map. -/
def diagonal (X : Graded k) : Homogeneous X X 0 := Correspondence.rationalGraph (𝟙 X.scheme)

/-- The diagonal correspondence is defined by the rational graph of `𝟙 X.scheme`. -/
theorem diagonal_def (X : Graded k) : diagonal X = Correspondence.rationalGraph (𝟙 X.scheme) := sorry

/-- The identity total morphism, concentrated in degree zero. -/
def identity (X : Graded k) : TotalHom X X := homogeneousInclusion X X 0 (diagonal X)

/-- The total identity is the homogeneous inclusion of the diagonal correspondence. -/
theorem identity_def (X : Graded k) : identity X = homogeneousInclusion X X 0 (diagonal X) := sorry

/-- Finite-support convolution of total correspondences by correspondence composition. -/
def comp {X Y Z : Graded k} (f : TotalHom X Y) (g : TotalHom Y Z) : TotalHom X Z :=
  let total : TotalHom Y Z →ₗ[ℚ] TotalHom X Y →ₗ[ℚ] TotalHom X Z :=
    DirectSum.toModule ℚ ℤ (TotalHom X Y →ₗ[ℚ] TotalHom X Z) fun s ↦
      { toFun := fun d ↦
          DirectSum.toModule ℚ ℤ (TotalHom X Z) fun r ↦
            (homogeneousInclusion X Z (r + s)).comp
              ((Correspondence.composition X.scheme Y.scheme Z.scheme r s).flip d)
        map_add' := sorry
        map_smul' := sorry }
  total g f

/-- Convolution on homogeneous inclusions is correspondence composition. -/
theorem comp_of_of {X Y Z : Graded k} {r s : ℤ} (c : Homogeneous X Y r) (d : Homogeneous Y Z s) :
    comp (homogeneousInclusion X Y r c) (homogeneousInclusion Y Z s d) =
      homogeneousInclusion X Z (r + s) (Correspondence.composition X.scheme Y.scheme Z.scheme r s c d) := sorry

/-- The category of smooth projective schemes with total rational correspondences. -/
@[reducible]
def category : CategoryTheory.Category.{u + 1} (Graded k) where
  Hom := TotalHom
  id := identity
  comp := comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The canonical category structure on smooth projective schemes with total rational correspondences. -/
instance instCategory : CategoryTheory.Category.{u + 1} (Graded k) := category

/-- Total rational correspondences form a preadditive category. -/
instance instPreadditive : Preadditive (Graded k) where
  homGroup X Y := inferInstanceAs (AddCommGroup (TotalHom X Y))
  add_comp := sorry
  comp_add := sorry

/-- The categorical identity is the degree-zero diagonal correspondence. -/
theorem id_eq (X : Graded k) : (𝟙 X : X ⟶ X) = homogeneousInclusion X X 0 (diagonal X) := sorry

/-- The degree-`r` submodule of a total correspondence Hom space. -/
def homDegree (X Y : Graded k) (r : ℤ) : Submodule ℚ (TotalHom X Y) :=
  (homogeneousInclusion X Y r).range

/-- The degree submodule is the range of the canonical homogeneous inclusion. -/
theorem homDegree_def (X Y : Graded k) (r : ℤ) : homDegree X Y r = (homogeneousInclusion X Y r).range := sorry

/-- A rational correspondence is canonically an element of its homogeneous submodule. -/
def homDegreeEquiv (X Y : Graded k) (r : ℤ) : Homogeneous X Y r ≃ₗ[ℚ] homDegree X Y r where
  toFun c := ⟨homogeneousInclusion X Y r c, ⟨c, rfl⟩⟩
  invFun c := DirectSum.component ℚ ℤ (fun i ↦ Homogeneous X Y i) r c.1
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_smul' := sorry

/-- The homogeneous-piece equivalence is induced by direct-sum inclusion. -/
theorem homDegreeEquiv_apply (X Y : Graded k) (r : ℤ) (c : Homogeneous X Y r) :
    homDegreeEquiv X Y r c =
      (⟨homogeneousInclusion X Y r c, ⟨c, rfl⟩⟩ : homDegree X Y r) := sorry

/-- The canonical integer-graded rational-linear category structure on correspondences. -/
instance instGradedCategory : GradedCategory ℚ (Graded k) ℤ where
  toLinear :=
    { homModule := fun X Y ↦ inferInstanceAs (Module ℚ (TotalHom X Y))
      smul_comp := sorry
      comp_smul := sorry }
  homDegree := homDegree
  homDecomposition := fun X Y ↦
    DirectSum.Decomposition.ofLinearMap (homDegree X Y)
      (DirectSum.toModule ℚ ℤ (⨁ r : ℤ, homDegree X Y r) fun r ↦
        (DirectSum.lof ℚ ℤ (fun i ↦ homDegree X Y i) r).comp (homDegreeEquiv X Y r).toLinearMap)
      sorry sorry
  id_mem_homDegree_zero := sorry
  comp_mem := sorry

end Graded

end AlgebraicGeometry.Correspondence
