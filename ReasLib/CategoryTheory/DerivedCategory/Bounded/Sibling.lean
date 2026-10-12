/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.EnoughNegativeObjects
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA vA uA vD uD

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [_root_.CategoryTheory.IsTriangulated D]

/-- Two exact triangulated functors out of a bounded derived category are siblings when
their restrictions along the degree-zero heart inclusion are naturally isomorphic and
they take every bounded derived object to isomorphic objects. -/
def areSiblings
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated] : Prop :=
  Nonempty
      (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F') ∧
    ∀ K : DerivedCategory.Bounded A, Nonempty (F.obj K ≅ F'.obj K)

/-- Sibling functors have naturally isomorphic restrictions to the degree-zero heart. -/
theorem areSiblings_restrict
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') :
    Nonempty
      (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F') := sorry

/-- Sibling functors take each bounded derived object to isomorphic objects. -/
theorem areSiblings_obj
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') (K : DerivedCategory.Bounded A) :
    Nonempty (F.obj K ≅ F'.obj K) := sorry

/-- Essential surjectivity transfers between sibling exact triangulated functors. -/
theorem essSurj_of_areSiblings
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') [F.EssSurj] : F'.EssSurj := sorry

/-- Full faithfulness transfers between sibling exact triangulated functors. -/
theorem fullyFaithful_of_areSiblings
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') (hF : Nonempty F.FullyFaithful) :
    Nonempty F'.FullyFaithful := sorry

/-- Every exact triangulated functor is sibling to itself. -/
theorem areSiblings_refl
    (F : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] : areSiblings F F := sorry

/-- Siblinghood is symmetric. -/
theorem areSiblings_symm
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : areSiblings F F') : areSiblings F' F := sorry

/-- Siblinghood is transitive. -/
theorem areSiblings_trans
    (F F' F'' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [F'.CommShift ℤ] [F'.IsTriangulated]
    [F''.CommShift ℤ] [F''.IsTriangulated]
    (h₁ : areSiblings F F') (h₂ : areSiblings F' F'') :
    areSiblings F F'' := sorry

/-- Exact triangulated functors with isomorphic restrictions to the heart and vanishing
negative shifted Homs between heart images are siblings. -/
theorem areSiblings_of_restrictIso_of_negShiftedHom
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (hiso : Nonempty (DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F ≅
        DerivedCategory.Bounded.singleFunctor A (0 : ℤ) ⋙ F'))
    (hvanish : ∀ (X Y : A) (q : ℤ), q < 0 →
      Subsingleton
        (ShiftedHom (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj X))
          (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj Y)) q)) :
    areSiblings F F' := sorry

/-- A fully faithful exact triangulated functor has subsingleton negative shifted Homs
between images of objects in the heart. -/
instance negShiftedHom_subsingleton_of_fullyFaithful
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (F : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]
    (X Y : A) (q : ℤ) [Fact (q < 0)] :
    Subsingleton
      (ShiftedHom (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj X))
        (F.obj ((DerivedCategory.Bounded.singleFunctor A (0 : ℤ)).obj Y)) q) := sorry

/-- Sibling exact triangulated functors from a bounded derived category are naturally
isomorphic if the abelian source has enough negative objects and the first functor
is fully faithful. -/
theorem isomorphic_of_areSiblings
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [_root_.CategoryTheory.IsTriangulated D]
    (hneg : HasEnoughNegativeObjects A)
    (F F' : DerivedCategory.Bounded A ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    [F.Full] [F.Faithful] (hsibling : areSiblings F F') :
    Nonempty (F ≅ F') := sorry

end CategoryTheory.Functor
