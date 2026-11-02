/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Graded.DegreeZero
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence.GradedCategory

variable {k : Type u} [Field k]

/-- Graded rational Chow correspondences form a preadditive category. -/
instance instPreadditive : Preadditive (GradedCategory k) where
  homGroup X Y := inferInstanceAs
    (AddCommGroup (Rational X.1.scheme Y.1.scheme (Y.2 - X.2)))
  add_comp := by
    change ∀ (X Y Z : GradedCategory k)
      (f g : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
      (h : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)),
      gradedComp (X := X) (Y := Y) (Z := Z) (f + g) h =
        gradedComp (X := X) (Y := Y) (Z := Z) f h +
          gradedComp (X := X) (Y := Y) (Z := Z) g h
    intro X Y Z f g h
    simp [GradedCategory.gradedComp]
  comp_add := by
    change ∀ (X Y Z : GradedCategory k)
      (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
      (g h : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)),
      gradedComp (X := X) (Y := Y) (Z := Z) f (g + h) =
        gradedComp (X := X) (Y := Y) (Z := Z) f g +
          gradedComp (X := X) (Y := Y) (Z := Z) f h
    intro X Y Z f g h
    simp [GradedCategory.gradedComp]

/-- Graded rational Chow correspondences form a `ℚ`-linear category. -/
instance instLinear : Linear ℚ (GradedCategory k) where
  homModule := fun X Y ↦ inferInstanceAs
    (Module ℚ (Rational X.1.scheme Y.1.scheme (Y.2 - X.2)))
  smul_comp := by
    change ∀ (X Y Z : GradedCategory k) (a : ℚ)
      (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2))
      (g : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)),
      gradedComp (X := X) (Y := Y) (Z := Z) (a • f) g =
        a • gradedComp (X := X) (Y := Y) (Z := Z) f g
    intro X Y Z a f g
    simp [GradedCategory.gradedComp]
  comp_smul := by
    change ∀ (X Y Z : GradedCategory k)
      (f : Rational X.1.scheme Y.1.scheme (Y.2 - X.2)) (a : ℚ)
      (g : Rational Y.1.scheme Z.1.scheme (Z.2 - Y.2)),
      gradedComp (X := X) (Y := Y) (Z := Z) f (a • g) =
        a • gradedComp (X := X) (Y := Y) (Z := Z) f g
    intro X Y Z f a g
    simp [GradedCategory.gradedComp]

end AlgebraicGeometry.Correspondence.GradedCategory

namespace AlgebraicGeometry.Correspondence.Graded

variable {k : Type u} [Field k]

private theorem castDegree_eq_transport_zero {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    {h : (0 : ℤ) = 0} (c : Rational X Y 0) :
    Correspondence.castDegree h c = h ▸ c := by
  cases h
  letI := BivariantClass.pointwiseAddCommGroup (fun _ ↦ 0)
    (CategoryTheory.Limits.prod.snd : X ⨯ Y ⟶ Y) 0
  change Correspondence.castDegree (rfl : (0 : ℤ) = 0) c = c
  induction c using TensorProduct.induction_on with
  | zero => exact (Correspondence.castDegree rfl).map_zero
  | tmul a c => simp [Correspondence.castDegree, BivariantClass.Nonnegative.castGrading]
  | add c d hc hd => simp only [map_add, hc, hd]

private theorem castDegree_zero {X Y : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (h : (0 : ℤ) = 0) (c : Rational X Y 0) :
    Correspondence.castDegree h c = c := by
  rw [castDegree_eq_transport_zero]

/-- Embed degree-zero correspondences into the twist-graded category at Tate twist zero. -/
def zeroTwistFunctor (k : Type u) [Field k] :
    DegreeZero (k := k) ⥤ Correspondence.GradedCategory k where
  obj X := Correspondence.GradedCategory.ofScheme X.obj.scheme 0
  map {X Y} f := degreeZeroHomEquiv X Y f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    simp only [degreeZeroHomEquiv]
    change DegreeZero.comp f g =
      Correspondence.GradedCategory.gradedComp
        (X := Correspondence.GradedCategory.ofScheme X.obj.scheme 0)
        (Y := Correspondence.GradedCategory.ofScheme Y.obj.scheme 0)
        (Z := Correspondence.GradedCategory.ofScheme Z.obj.scheme 0) f g
    change Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g =
      Correspondence.castDegree (Correspondence.GradedCategory.degree_comp 0 0 0)
        (Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g)
    exact (castDegree_zero (Correspondence.GradedCategory.degree_comp 0 0 0)
      (Correspondence.composition X.obj.scheme Y.obj.scheme Z.obj.scheme 0 0 f g)).symm

/-- The zero-twist functor places the underlying smooth projective scheme in twist zero. -/
theorem zeroTwistFunctor_obj (X : DegreeZero (k := k)) :
    (zeroTwistFunctor k).obj X =
      Correspondence.GradedCategory.ofScheme X.obj.scheme 0 := rfl

/-- The zero-twist functor sends a degree-zero morphism to its rational correspondence. -/
theorem zeroTwistFunctor_map {X Y : DegreeZero (k := k)} (f : X ⟶ Y) :
    (zeroTwistFunctor k).map f =
      degreeZeroHomEquiv X Y f := rfl

end AlgebraicGeometry.Correspondence.Graded
