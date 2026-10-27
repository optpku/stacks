/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Opposites

/-!
# Opposite transport for standard fibres

Fibre objects and their automorphisms admit concrete transport to and from the
fibres of the opposite projection.
-/

@[expose] public section

open CategoryTheory Opposite

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {F : Type u₂} [Category.{v₂} F]

namespace CategoryTheory.Functor.Fiber

/-- The standard fibre object determined by an object of the total category. -/
def ofObj (p : F ⥤ C) (x : F) : p.Fiber (p.obj x) := ⟨x, rfl⟩

/-- The underlying total-category object of `ofObj p x` is `x`. -/
theorem ofObj_coe (p : F ⥤ C) (x : F) : (ofObj p x).1 = x := rfl

/-- The object of `p.op.Fiber (op U)` corresponding to an object of `p.Fiber U`. -/
def toOp {p : F ⥤ C} {U : C} (x : p.Fiber U) : p.op.Fiber (op U) :=
  ⟨op x.1, congrArg op x.2⟩

/-- The object of `p.Fiber U` corresponding to an object of `p.op.Fiber (op U)`. -/
def fromOp {p : F ⥤ C} {U : C} (x : p.op.Fiber (op U)) : p.Fiber U :=
  ⟨x.1.unop, Opposite.op_injective x.2⟩

/-- Converting a fibre object to the opposite fibre and back recovers the object. -/
theorem fromOp_toOp {p : F ⥤ C} {U : C} (x : p.Fiber U) : fromOp (toOp x) = x := rfl

/-- Converting an opposite fibre object to the original fibre and back recovers the object. -/
theorem toOp_fromOp {p : F ⥤ C} {U : C} (x : p.op.Fiber (op U)) : toOp (fromOp x) = x := rfl

/-- The identity comparison `toOp (fromOp y) ≅ y` on the common total-category object. -/
def toOpFromOpIso {p : F ⥤ C} {U : C} (y : p.op.Fiber (op U)) : toOp (fromOp y) ≅ y :=
  isoMk (Iso.refl y.1) (IsHomLift.id y.2)

/-- The identity comparison `fromOp (toOp x) ≅ x` on the common total-category object. -/
def fromOpToOpIso {p : F ⥤ C} {U : C} (x : p.Fiber U) : fromOp (toOp x) ≅ x :=
  isoMk (Iso.refl x.1) (IsHomLift.id x.2)

/-- The forward map of `toOpFromOpIso` is the identity on the underlying total-category object. -/
theorem toOpFromOpIso_hom {p : F ⥤ C} {U : C} (y : p.op.Fiber (op U)) :
    (toOpFromOpIso y).hom.1 = 𝟙 y.1 := rfl

/-- The forward map of `fromOpToOpIso` is the identity on the underlying total-category object. -/
theorem fromOpToOpIso_hom {p : F ⥤ C} {U : C} (x : p.Fiber U) :
    (fromOpToOpIso x).hom.1 = 𝟙 x.1 := rfl

/-- The opposite of the underlying isomorphism of a fibre automorphism is vertical. -/
theorem toOpAut_isHomLift {p : F ⥤ C} {U : C} {x : p.Fiber U} (α : Aut x) :
    p.op.IsHomLift (𝟙 (op U)) (Iso.op (fiberInclusion.mapIso α)).hom := by
  have opLift {V W : C} {a b : F} {f : V ⟶ W} {φ : a ⟶ b}
      (h : p.IsHomLift f φ) : p.op.IsHomLift f.op φ.op := by
    cases h
    exact IsHomLift.map _
  exact opLift α.hom.2

/-- The unopposite of the underlying isomorphism of an opposite-fibre automorphism is vertical. -/
theorem fromOpAut_isHomLift {p : F ⥤ C} {U : C} {y : p.op.Fiber (op U)} (α : Aut y) :
    p.IsHomLift (𝟙 U) (Iso.unop (fiberInclusion.mapIso α)).hom := by
  have unopLift {V W : Cᵒᵖ} {a b : Fᵒᵖ} {f : V ⟶ W} {φ : a ⟶ b}
      (h : p.op.IsHomLift f φ) : p.IsHomLift f.unop φ.unop := by
    cases h
    exact IsHomLift.map _
  exact unopLift α.hom.2

/-- Opposite of a fibre automorphism, as an automorphism of the opposite fibre object. -/
def toOpAut {p : F ⥤ C} {U : C} {x : p.Fiber U} (α : Aut x) : Aut (toOp x) :=
  isoMk (Iso.op (fiberInclusion.mapIso α)) (toOpAut_isHomLift α)

/-- Unopposite of an opposite-fibre automorphism, as an automorphism of the original fibre. -/
def fromOpAut {p : F ⥤ C} {U : C} {y : p.op.Fiber (op U)} (α : Aut y) : Aut (fromOp y) :=
  isoMk (Iso.unop (fiberInclusion.mapIso α)) (fromOpAut_isHomLift α)

/-- The underlying total arrow of `toOpAut α` is the opposite of the underlying arrow of `α`. -/
theorem toOpAut_hom {p : F ⥤ C} {U : C} {x : p.Fiber U} (α : Aut x) :
    (toOpAut α).hom.1 = α.hom.1.op := rfl

/-- The underlying total arrow of `fromOpAut α` is the unopposite of the underlying arrow of `α`. -/
theorem fromOpAut_hom {p : F ⥤ C} {U : C} {y : p.op.Fiber (op U)} (α : Aut y) :
    (fromOpAut α).hom.1 = α.hom.1.unop := rfl

end CategoryTheory.Functor.Fiber
