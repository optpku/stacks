/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Functor.Forget

/-!
# Functorial Brutal Postnikov Towers

This leaf owns the brutal Postnikov-tower functor, its finite restrictions,
and their basic object, morphism, and forgetful computations.
-/

@[expose] public section

open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.CochainComplex.Brutal.Derived.Postnikov

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

variable (A) in
/-- The functor sending a cochain complex strictly supported in degrees at most zero to its
canonical brutal Postnikov tower. -/
@[stacks 0D8Z "functorial brutal Postnikov tower"]
noncomputable def functor :
    CochainComplex.StrictlyLE A 0 ⥤
      PostnikovSystem.Tower (DerivedCategory A) where
  obj K := tower K.obj
  map f := map f.hom
  map_id K := map_id K.obj
  map_comp f g := map_comp f.hom g.hom

/-- The object selected by the brutal Postnikov functor is the canonical tower of the underlying
cochain complex. -/
@[simp, stacks 0D8Z]
theorem functor_obj (K : CochainComplex.StrictlyLE A 0) :
    (functor A).obj K = tower K.obj := sorry

/-- The brutal Postnikov functor maps a bounded-complex morphism by the canonical tower map on
its underlying cochain map. -/
@[simp, stacks 0D8Z]
theorem functor_map {K L : CochainComplex.StrictlyLE A 0} (f : K ⟶ L) :
    (functor A).map f = map f.hom := sorry

namespace Finite

variable (A) in
/-- The finite total Postnikov-system functor at length `n`, obtained from the brutal Postnikov
tower functor by generic finite restriction. -/
@[stacks 0D8Z "functorial finite brutal Postnikov system"]
noncomputable def functor (n : ℕ) :
    CochainComplex.StrictlyLE A 0 ⥤ PostnikovSystem.Total (DerivedCategory A) n :=
  _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.functor A ⋙
    PostnikovSystem.Tower.finiteFunctor (DerivedCategory A) n

/-- The base of a finite functor value is the reversed finite brutal row. -/
@[simp, stacks 0D8Z]
theorem functor_obj_base (n : ℕ) (K : CochainComplex.StrictlyLE A 0) :
    ((functor A n).obj K).base = row K.obj n := sorry

/-- The system carried by a finite functor value is the finite brutal Postnikov system. -/
@[simp, stacks 0D8Z]
theorem functor_obj_system (n : ℕ) (K : CochainComplex.StrictlyLE A 0) :
    ((functor A n).obj K).system = system K.obj n := sorry

/-- The base component of a finite functor map is restriction of the induced tower morphism to
the finite row. -/
@[simp, stacks 0D8Z]
theorem functor_map_base (n : ℕ) {K L : CochainComplex.StrictlyLE A 0} (f : K ⟶ L) :
    ((functor A n).map f).base =
      (Postnikov.map f.hom).row n := sorry

/-- The system component of a finite functor map is the canonical finite brutal
Postnikov-system morphism. -/
@[simp, stacks 0D8Z]
theorem functor_map_systemMap (n : ℕ) {K L : CochainComplex.StrictlyLE A 0} (f : K ⟶ L) :
    ((functor A n).map f).systemMap = map f.hom n := sorry

/-- Forgetting the finite Postnikov system from finite brutal restriction retains exactly the
generic finite-row restriction of the brutal Postnikov tower. -/
@[stacks 0D8Z "underlying row of the functorial finite brutal Postnikov system"]
theorem functor_comp_forget (n : ℕ) :
    functor A n ⋙ PostnikovSystem.Total.forget (DerivedCategory A) n =
      _root_.CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.functor A ⋙
        PostnikovSystem.Tower.rowFunctor (DerivedCategory A) n := sorry

end Finite

end CategoryTheory.CochainComplex.Brutal.Derived.Postnikov
