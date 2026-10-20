module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Tower
public import ReasLib.CategoryTheory.MorphismProperty.IsPreservedBy
public import ReasLib.CategoryTheory.Pro.Sequential.Shift

@[expose] public section

/-!
# Pro-Isomorphisms of Derived Sequential Inverse Systems

@stack 091B

This module defines the pro-object realization of the stagewise tower and its
induced morphism property. It does not depend on a model for derived inverse
limit.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

namespace Pro

/-- The pro-object realization of a derived sequential inverse system, obtained
by applying derived evaluation stagewise and then taking the associated
sequential pro-object. -/
@[stacks 091B]
noncomputable abbrev realization (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wSys} (SequentialInverseSystem A)] :
    DerivedCategory (SequentialInverseSystem A) ⥤
      _root_.CategoryTheory.Pro.{max u v, wA} (DerivedCategory A) :=
  Stage.towerFunctor A ⋙
    _root_.CategoryTheory.Pro.lim (C := DerivedCategory A) ℕᵒᵖ

/-- The sequential pro-morphism representative induced by the stagewise tower
map of a derived morphism. -/
@[stacks 091B]
def representative {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L) :
    _root_.CategoryTheory.Pro.SequentialHom (Stage.tower K) (Stage.tower L) :=
  _root_.CategoryTheory.Pro.SequentialHom.ofNatTrans
    ((Stage.towerFunctor A).map f)

/-- The concrete sequential representative presents the morphism assigned by
the pro-object realization functor. -/
@[simp]
theorem representative_toHom
    {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L) :
    (representative f).toHom = (realization A).map f := sorry

/-- The morphism property of maps of derived sequential inverse systems that
become isomorphisms between their stagewise pro-objects. -/
@[stacks 091B]
noncomputable abbrev isomorphisms (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wSys} (SequentialInverseSystem A)] :
    MorphismProperty.{wSys, max u v}
      (DerivedCategory (SequentialInverseSystem A)) :=
  (MorphismProperty.isomorphisms
      (_root_.CategoryTheory.Pro (DerivedCategory A))).inverseImage
    (realization A)

/-- Membership in `Pro.isomorphisms` can be checked on the canonical concrete
sequential representative. -/
@[simp]
theorem mem_isomorphisms_iff
    {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L) :
    isomorphisms A f ↔
      _root_.CategoryTheory.IsIso (representative f).toHom := sorry

end Pro

end CategoryTheory.DerivedLimit
