/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sheaves graded by a constant sheaf

A sheaf of `β`-graded types is modeled source-faithfully as a type-valued sheaf equipped with a
map to the constant sheaf on `β`.  Taking degree fibers converts this total-space presentation to
the canonical `GradedObject β (Sheaf J (Type w))` presentation used by pointwise constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type w)]

/-- The constant type-valued sheaf carrying the grading values. -/
abbrev gradingSheaf (β : Type w) : Sheaf J (Type w) :=
  (constantSheaf J (Type w)).obj β

/-- A `β`-graded sheaf is a type-valued sheaf with a degree map to the constant sheaf on `β`. -/
@[stacks 0FSF "sheaves of graded types"]
abbrev GradedSheaf (β : Type w) := Over (gradingSheaf J β)

namespace GradedSheaf

variable {J} {β : Type w}

/-- The underlying type-valued sheaf of a graded sheaf. -/
abbrev toSheaf (S : GradedSheaf J β) : Sheaf J (Type w) := S.left

/-- The degree morphism of a graded sheaf. -/
abbrev degree (S : GradedSheaf J β) : S.toSheaf ⟶ gradingSheaf J β := S.hom

/-- Sections of a graded sheaf over an object of the site. -/
abbrev sections (S : GradedSheaf J β) (U : Cᵒᵖ) : Type w := S.toSheaf.obj.obj U

/-- The locally constant section of the grading sheaf determined by `b : β`. -/
noncomputable def constantSection (U : Cᵒᵖ) (b : β) :
    (gradingSheaf J β).obj.obj U :=
  (toSheafify J ((Functor.const Cᵒᵖ).obj β)).app U b

/-- The degree of a local section, viewed as a local section of the grading sheaf. -/
abbrev sectionDegree (S : GradedSheaf J β) (U : Cᵒᵖ) (s : S.sections U) :
    (gradingSheaf J β).obj.obj U :=
  S.degree.hom.app U s

/-- The presheaf of local sections having a specified degree. -/
noncomputable def degreeFiberPresheaf (S : GradedSheaf J β) (b : β) : Cᵒᵖ ⥤ Type w where
  obj U := {s : S.sections U // S.sectionDegree U s = constantSection U b}
  map {U V} f :=
    ↾fun s ↦ ⟨S.toSheaf.obj.map f s.1, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- The presheaf of sections of a fixed degree satisfies the sheaf condition. -/
theorem degreeFiberPresheaf_isSheaf (S : GradedSheaf J β) (b : β) :
    Presheaf.IsSheaf J (degreeFiberPresheaf S b) := sorry

/-- The sheaf of local sections having a specified degree. -/
@[stacks 0FSF "degree fibers of a graded sheaf"]
noncomputable def degreeFiber (S : GradedSheaf J β) (b : β) : Sheaf J (Type w) :=
  ⟨degreeFiberPresheaf S b, degreeFiberPresheaf_isSheaf S b⟩

/-- Sections of `degreeFiber S b` are exactly sections of `S` whose degree is `b`. -/
@[simp]
theorem degreeFiber_obj (S : GradedSheaf J β) (U : Cᵒᵖ) (b : β) :
    (degreeFiber S b).obj.obj U =
      {s : S.sections U // S.sectionDegree U s = constantSection U b} := sorry

/-- A morphism of graded sheaves restricts to a morphism on each degree fiber. -/
noncomputable def degreeFiberMap {S T : GradedSheaf J β} (f : S ⟶ T) (b : β) :
    degreeFiber S b ⟶ degreeFiber T b :=
  ObjectProperty.homMk
    { app := fun U ↦ ↾fun s ↦ ⟨f.left.hom.app U s.1, sorry⟩
      naturality := fun _ _ g ↦ sorry }

/-- Degree fibers assemble into a functor from total graded sheaves to graded objects in sheaves. -/
@[stacks 0FSF "degree-fiber functor for graded sheaves"]
noncomputable def degreeFiberFunctor :
    GradedSheaf J β ⥤ GradedObject β (Sheaf J (Type w)) where
  obj S b := degreeFiber S b
  map f b := degreeFiberMap f b
  map_id := sorry
  map_comp := sorry

/-- The degree-`b` component of the degree-fiber functor is `degreeFiber S b`. -/
@[simp]
theorem degreeFiberFunctor_obj (S : GradedSheaf J β) (b : β) :
    degreeFiberFunctor.obj S b = degreeFiber S b := sorry

/-- The degree-`b` component of a mapped morphism is the restricted degree-fiber map. -/
@[simp]
theorem degreeFiberFunctor_map {S T : GradedSheaf J β} (f : S ⟶ T) (b : β) :
    degreeFiberFunctor.map f b = degreeFiberMap f b := sorry

end GradedSheaf

/-- A sheaf graded by a small type `β`, represented in `Type w` by its canonical universe lift. -/
@[stacks 0FSF "sheaves graded by a small type"]
abbrev SmallGradedSheaf (β : Type) := GradedSheaf J (ULift.{w} β)

/-- An integer-graded sheaf, with the universe lift of `ℤ` hidden from the public interface. -/
@[stacks 0FSF "integer-graded sheaves"]
abbrev IntGradedSheaf := SmallGradedSheaf J ℤ

namespace SmallGradedSheaf

variable {J} {β : Type}

/-- The sheaf of local sections of a small-graded sheaf having degree `b`. -/
abbrev degreeFiber (S : SmallGradedSheaf J β) (b : β) : Sheaf J (Type w) :=
  GradedSheaf.degreeFiber S (ULift.up b)

/-- A morphism of small-graded sheaves restricts to every small degree fiber. -/
noncomputable def degreeFiberMap {S T : SmallGradedSheaf J β} (f : S ⟶ T) (b : β) :
    degreeFiber S b ⟶ degreeFiber T b :=
  GradedSheaf.degreeFiberMap f (ULift.up b)

/-- Degree fibers of a small-graded sheaf form a graded object indexed by the original small type. -/
@[stacks 0FSF "degree-fiber functor for small-graded sheaves"]
noncomputable def degreeFiberFunctor :
    SmallGradedSheaf J β ⥤ GradedObject β (Sheaf J (Type w)) where
  obj S b := degreeFiber S b
  map f b := degreeFiberMap f b
  map_id := sorry
  map_comp := sorry

/-- The degree-`b` component of the small degree-fiber functor is `degreeFiber S b`. -/
@[simp]
theorem degreeFiberFunctor_obj (S : SmallGradedSheaf J β) (b : β) :
    degreeFiberFunctor.obj S b = degreeFiber S b := sorry

/-- The degree-`b` component of a mapped small-graded morphism is its fiber restriction. -/
@[simp]
theorem degreeFiberFunctor_map {S T : SmallGradedSheaf J β} (f : S ⟶ T) (b : β) :
    degreeFiberFunctor.map f b = degreeFiberMap f b := sorry

end SmallGradedSheaf

end CategoryTheory

end
