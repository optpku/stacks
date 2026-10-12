/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.AddCommGrp.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic functorial extension groups

This leaf owns the representation-independent functorial layer for derived Ext.  The target
variable is covariant, the source variable is represented on the opposite derived category, and
the bundled bifunctor records both actions.  Filtered specializations live in the sibling
`Filtered` leaf.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated ShiftedHom
open scoped DerivedExt

noncomputable section

universe t w v u

namespace CategoryTheory.DerivedCategory.Ext

section Derived

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A]

namespace Target

/-- The target-variable functor `Ext⁽n⁾(M, -)` on the derived category.

This is a thin semantic name for the neutral `ShiftedHom.AddCommGrp.targetFunctor` owner; no
second functorial construction is introduced at the derived-category layer. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
abbrev functor (M : DerivedCategory A) (n : ℤ) :
    DerivedCategory A ⥤ AddCommGrpCat.{t} :=
  ShiftedHom.AddCommGrp.targetFunctor M n

/-- The object computation for the target-variable Ext functor. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem functor_obj (M K : DerivedCategory A) (n : ℤ) :
    (functor M n).obj K = addCommGrp M K n := rfl

/-- The morphism computation for the target-variable Ext functor. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem functor_map {M K L : DerivedCategory A} (n : ℤ) (f : K ⟶ L) :
    (functor M n).map f = ShiftedHom.postcomp M f n := rfl

end Target

namespace Source

/-!
The source-variable entry is presented on the opposite derived category, so its ordinary map
direction agrees with categorical composition.  This is the canonical variance-neutral surface;
source-filtered constructions can use it without introducing ad hoc reversed maps.
-/

/-- The source-variable functor `Ext⁽n⁾(-, K)` on the opposite derived category.

The actual functor is the neutral `ShiftedHom.AddCommGrp.sourceFunctor` owner. -/
@[stacks 0G1X, stacks 0G1Z]
abbrev functor (K : DerivedCategory A) (n : ℤ) :
    (DerivedCategory A)ᵒᵖ ⥤ AddCommGrpCat.{t} :=
  ShiftedHom.AddCommGrp.sourceFunctor K n

@[simp, stacks 0G1X, stacks 0G1Z]
theorem functor_obj (K : DerivedCategory A) (n : ℤ) (M : (DerivedCategory A)ᵒᵖ) :
    (functor K n).obj M = addCommGrp M.unop K n := rfl

@[simp, stacks 0G1X, stacks 0G1Z]
theorem functor_map {K : DerivedCategory A} {M N : (DerivedCategory A)ᵒᵖ}
    (n : ℤ) (f : M ⟶ N) :
    (functor K n).map f = ShiftedHom.precomp f.unop K n := rfl

end Source

/-- The derived Ext bifunctor, contravariant in the first variable and covariant in the second.

Its data is owned by the neutral `ShiftedHom.AddCommGrp.bifunctor`; this name retains the
derived-category vocabulary for existing clients. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
abbrev functor (n : ℤ) :
    (DerivedCategory A)ᵒᵖ ⥤ (DerivedCategory A ⥤ AddCommGrpCat.{t}) :=
  ShiftedHom.AddCommGrp.bifunctor n

@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem functor_obj (n : ℤ) (M : (DerivedCategory A)ᵒᵖ) :
    (functor n).obj M = Target.functor M.unop n := rfl

@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem functor_map_app (n : ℤ) {M N : (DerivedCategory A)ᵒᵖ}
    (f : M ⟶ N) (K : DerivedCategory A) :
    ((functor n).map f).app K = ShiftedHom.precomp f.unop K n := rfl

/-- Evaluating both variables of the Ext bifunctor recovers the bundled shifted Hom group. -/
@[simp, stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
theorem functor_obj_obj (n : ℤ) (M : (DerivedCategory A)ᵒᵖ)
    (K : DerivedCategory A) :
    ((functor n).obj M).obj K = addCommGrp M.unop K n := rfl

/-- The source action of the Ext bifunctor is `Source.functor`. -/
@[simp, stacks 0G1X, stacks 0G1Z]
theorem functor_map_app_source (n : ℤ) {M N : (DerivedCategory A)ᵒᵖ}
    (f : M ⟶ N) (K : DerivedCategory A) :
    ((functor n).map f).app K = (Source.functor K n).map f := rfl

/-- The mixed-variance naturality square for derived Ext. -/
@[reassoc, stacks 0G1X, stacks 0G1Z]
theorem functor_map_naturality (n : ℤ) {M N : (DerivedCategory A)ᵒᵖ}
    (f : M ⟶ N) {K L : DerivedCategory A} (g : K ⟶ L) :
    ((functor n).map f).app K ≫ (Target.functor N.unop n).map g =
      (Target.functor M.unop n).map g ≫ ((functor n).map f).app L := sorry

end Derived

end CategoryTheory.DerivedCategory.Ext
