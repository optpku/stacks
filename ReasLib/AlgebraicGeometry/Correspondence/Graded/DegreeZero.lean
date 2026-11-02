/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Graded

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry DirectSum TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.Graded

variable {k : Type u} [Field k]

/-- The degree-zero correspondence category has the same smooth projective objects. -/
inductive DegreeZero (k : Type u) [Field k] where
  /-- View a graded correspondence object in the degree-zero category. -/
  | mk (X : Graded k)

namespace DegreeZero

/-- The graded correspondence object underlying a degree-zero object. -/
def obj : DegreeZero k → Graded k
  | .mk X => X

/-- Composition of degree-zero correspondences. -/
def comp {X Y Z : DegreeZero k} (f : Graded.Homogeneous X.obj Y.obj 0)
    (g : Graded.Homogeneous Y.obj Z.obj 0) : Graded.Homogeneous X.obj Z.obj 0 :=
  Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g

/-- The diagonal correspondence is the identity morphism. -/
def identity (X : DegreeZero k) : Graded.Homogeneous X.obj X.obj 0 := Graded.diagonal X.obj

/-- Degree-zero rational correspondences form a category. -/
@[reducible]
def category : CategoryTheory.Category (DegreeZero k) where
  Hom := fun X Y ↦ Graded.Homogeneous X.obj Y.obj 0
  id := identity
  comp := comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The canonical category structure on degree-zero rational correspondences. -/
instance instCategory : CategoryTheory.Category (DegreeZero k) := category

/-- Degree-zero rational correspondences form a preadditive category. -/
instance instPreadditive : Preadditive (DegreeZero k) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Graded.Homogeneous X.obj Y.obj 0))
  add_comp := by
    intro X Y Z f₁ f₂ g
    letI : AddCommGroup (X ⟶ Y) :=
      inferInstanceAs (AddCommGroup (Graded.Homogeneous X.obj Y.obj 0))
    letI : AddCommGroup (Y ⟶ Z) :=
      inferInstanceAs (AddCommGroup (Graded.Homogeneous Y.obj Z.obj 0))
    letI : AddCommGroup (X ⟶ Z) :=
      inferInstanceAs (AddCommGroup (Graded.Homogeneous X.obj Z.obj 0))
    change Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0
        (f₁ + f₂) g =
      Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f₁ g +
        Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f₂ g
    simp only [map_add, LinearMap.add_apply]
  comp_add := by
    intro X Y Z f g₁ g₂
    letI : AddCommGroup (X ⟶ Y) :=
      inferInstanceAs (AddCommGroup (Graded.Homogeneous X.obj Y.obj 0))
    letI : AddCommGroup (Y ⟶ Z) :=
      inferInstanceAs (AddCommGroup (Graded.Homogeneous Y.obj Z.obj 0))
    letI : AddCommGroup (X ⟶ Z) :=
      inferInstanceAs (AddCommGroup (Graded.Homogeneous X.obj Z.obj 0))
    change Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f
        (g₁ + g₂) =
      Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g₁ +
        Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g₂
    exact map_add (Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f) g₁ g₂

/-- The degree-zero correspondence category is rational-linear. -/
instance instLinear : Linear ℚ (DegreeZero k) where
  homModule := fun X Y ↦ inferInstanceAs (Module ℚ (Graded.Homogeneous X.obj Y.obj 0))
  smul_comp := by
    intro X Y Z a f g
    letI : Module ℚ (X ⟶ Y) :=
      inferInstanceAs (Module ℚ (Graded.Homogeneous X.obj Y.obj 0))
    letI : Module ℚ (Y ⟶ Z) :=
      inferInstanceAs (Module ℚ (Graded.Homogeneous Y.obj Z.obj 0))
    letI : Module ℚ (X ⟶ Z) :=
      inferInstanceAs (Module ℚ (Graded.Homogeneous X.obj Z.obj 0))
    change Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 (a • f) g =
      a • Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g
    simp only [map_smul, LinearMap.smul_apply]
  comp_smul := by
    intro X Y Z f a g
    letI : Module ℚ (X ⟶ Y) :=
      inferInstanceAs (Module ℚ (Graded.Homogeneous X.obj Y.obj 0))
    letI : Module ℚ (Y ⟶ Z) :=
      inferInstanceAs (Module ℚ (Graded.Homogeneous Y.obj Z.obj 0))
    letI : Module ℚ (X ⟶ Z) :=
      inferInstanceAs (Module ℚ (Graded.Homogeneous X.obj Z.obj 0))
    change Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f (a • g) =
      a • Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g
    exact map_smul (Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f) a g

end DegreeZero

/-- The direct degree-zero Hom representation is canonically linearly equivalent to the homogeneous space. -/
def degreeZeroHomEquiv (X Y : DegreeZero k) : (X ⟶ Y) ≃ₗ[ℚ] Graded.Homogeneous X.obj Y.obj 0 where
  toFun f := f
  invFun c := c
  left_inv := by intro f; rfl
  right_inv := by intro c; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The degree-zero Hom equivalence evaluates to the underlying correspondence. -/
theorem degreeZeroHomEquiv_apply (X Y : DegreeZero k) (f : X ⟶ Y) :
    degreeZeroHomEquiv X Y f = f := rfl

end AlgebraicGeometry.Correspondence.Graded
