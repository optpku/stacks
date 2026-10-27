/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.AbsoluteMaps
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids.RelativeMaps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolute inertia maps of setoid stacks

The absolute forgetful map and identity section, their groupoid-stack and setoid-fibred
computations, and the resulting objectwise equivalence.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.inertia

/-- Forget the selected automorphism from bundled absolute inertia. -/
@[stacks 042H "setoid-stack inertia structure map"]
def forget (X : StackOver.Setoids.{u, v, max w vS, vS} J) : inertia X ⟶ X :=
  Hom.lift (StackOver.Groupoids.inertia.forget X.toGroupoids)

/-- The underlying groupoid-stack morphism is neutral inertia forgetting. -/
@[simp, stacks 042H "setoid-stack inertia structure-map readout"]
theorem forget.hom (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    (forget X).hom = StackOver.Groupoids.inertia.forget X.toGroupoids := by
  rfl

/-- The setoid-fibred morphism is neutral inertia forgetting. -/
@[simp, stacks 042H "setoid-fibred inertia structure-map readout"]
theorem forget.toSetoidsMor (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    Hom.toSetoidsMor (forget X) =
      FiberedCategoryOver.Setoids.Inertia.forget X.toSetoids := by
  rfl

/-- Equip every object of a setoid stack with its identity automorphism. -/
@[stacks 04Z3 "setoid-stack inertia neutral section"]
def identitySection
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) : X ⟶ inertia X :=
  Hom.lift (StackOver.Groupoids.inertia.identitySection X.toGroupoids)

/-- The underlying groupoid-stack morphism is the neutral identity section. -/
@[simp, stacks 04Z3 "setoid-stack inertia neutral-section readout"]
theorem identitySection.hom
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    (identitySection X).hom =
      StackOver.Groupoids.inertia.identitySection X.toGroupoids := by
  rfl

/-- The setoid-fibred morphism is the canonical neutral identity section. -/
@[simp, stacks 04Z3 "setoid-fibred inertia neutral-section readout"]
theorem identitySection.toSetoidsMor
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    Hom.toSetoidsMor (identitySection X) =
      FiberedCategoryOver.Setoids.Inertia.identitySection X.toSetoids := by
  rfl

/-- The inertia identity section is a right inverse to inertia forgetting. -/
@[simp, stacks 04Z3 "setoid-stack inertia section/forget readout"]
theorem identitySection.comp_forget
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    identitySection X ≫ forget X = 𝟙 X := by
  rfl

/-- Thin fibres make inertia forgetting a left inverse to the identity section. -/
@[simp, stacks 04Z3 "setoid-stack inertia forget/section readout"]
theorem forget.comp_identitySection
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    forget X ≫ identitySection X = 𝟙 (inertia X) := by
  have hAut (A : RelativeInertia X.p) : A.aut = 1 := by
    apply Iso.ext
    apply X.2.toFaithful.map_injective
    exact (congrArg Iso.hom A.2).trans (X.p.map_id A.obj).symm
  have hobj (A : RelativeInertia X.p) :
      RelativeInertia.identitySection.obj X.p A.obj = A := by
    apply Subtype.ext
    exact Sigma.ext rfl (heq_of_eq (hAut A).symm)
  have hfun :
      RelativeInertia.forget X.p ⋙ RelativeInertia.identitySection X.p =
        𝟭 (RelativeInertia X.p) := by
    refine Functor.hext hobj ?_
    intro A B f
    rcases A with ⟨⟨a, α⟩, ha⟩
    rcases B with ⟨⟨b, β⟩, hb⟩
    have hα := hAut ⟨⟨a, α⟩, ha⟩
    have hβ := hAut ⟨⟨b, β⟩, hb⟩
    change α = 1 at hα
    change β = 1 at hβ
    subst α
    subst β
    rfl
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  have hinj : Function.Injective
      (fun F : BasedFunctor (BasedCategory.inertia X.toBasedCategory)
        (BasedCategory.inertia X.toBasedCategory) ↦ F.toFunctor) := by
    intro F G h
    cases F
    cases G
    cases h
    rfl
  exact hinj hfun

/-- Absolute inertia of a stack in setoids is canonically equivalent to the original stack. -/
@[stacks 04Z3 "setoid-stack inertia equivalence"]
def forget.equivalence
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) : inertia X ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (ObjectProperty.FullSubbicategory.equivalenceOfAmbient
      (ObjectProperty.FullSubbicategory.equivalenceOfAmbient
        (BasedCategory.Inertia.forget.equivalenceOf X.toBasedCategory X.2)))

/-- The forward morphism of the inertia equivalence is forgetting. -/
@[simp, stacks 04Z3 "setoid-stack inertia equivalence forward readout"]
theorem forget.equivalence.hom
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    (forget.equivalence X).hom = forget X := by
  rfl

/-- The inverse morphism of the inertia equivalence is the identity section. -/
@[simp, stacks 04Z3 "setoid-stack inertia equivalence inverse readout"]
theorem forget.equivalence.inv
    (X : StackOver.Setoids.{u, v, max w vS, vS} J) :
    (forget.equivalence X).inv = identitySection X := by
  rfl

end StackOver.Setoids.inertia

namespace StackOver.Setoids.relativeInertia

variable {X Y : StackOver.Setoids.{u, v, max w vS, vS} J}

/-- Retaining and then forgetting a relative automorphism agrees with direct forgetting. -/
@[simp, stacks 04Z5 "setoid-stack relative-to-absolute inertia comparison"]
theorem toInertia.comp_forget (F : X ⟶ Y) :
    toInertia F ≫ inertia.forget X = forget F := by
  rfl

/-- The relative identity section followed by retention is the absolute identity section. -/
@[simp, stacks 04Z5 "setoid-stack relative-to-absolute neutral section comparison"]
theorem identitySection.comp_toInertia (F : X ⟶ Y) :
    identitySection F ≫ toInertia F = inertia.identitySection X := by
  rfl

end StackOver.Setoids.relativeInertia

end CategoryTheory
