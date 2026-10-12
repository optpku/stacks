/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Basic.RelativeMaps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolute inertia maps of stacks

The absolute forgetful map and identity section, together with the comparison equations linking
them to relative inertia.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.inertia

/-- Forget the selected automorphism from bundled absolute inertia. -/
@[stacks 042H "stack inertia structure map"]
def forget (X : StackOver.{u, v, max w vS, vS} J) : inertia X ⟶ X :=
  Hom.lift (FiberedCategoryOver.Inertia.forget X.toFiberedCategoryOver)

/-- The ambient fibered morphism is neutral inertia forgetting. -/
@[simp, stacks 042H "underlying stack inertia forgetful morphism"]
theorem forget.hom (X : StackOver.{u, v, max w vS, vS} J) :
    (forget X).hom =
      FiberedCategoryOver.Inertia.forget X.toFiberedCategoryOver := sorry

/-- Equip every object of a stack with its identity automorphism. -/
@[stacks 04Z3 "stack inertia neutral section"]
def identitySection (X : StackOver.{u, v, max w vS, vS} J) : X ⟶ inertia X :=
  Hom.lift (FiberedCategoryOver.Inertia.identitySection X.toFiberedCategoryOver)

/-- The ambient fibered morphism is the canonical neutral identity section. -/
@[simp, stacks 04Z3 "underlying stack inertia identity section"]
theorem identitySection.hom (X : StackOver.{u, v, max w vS, vS} J) :
    (identitySection X).hom =
      FiberedCategoryOver.Inertia.identitySection X.toFiberedCategoryOver := sorry

/-- The inertia identity section is a right inverse to inertia forgetting. -/
@[simp, stacks 04Z3 "stack inertia identity-section round trip"]
theorem identitySection.comp_forget
    (X : StackOver.{u, v, max w vS, vS} J) :
    identitySection X ≫ forget X = 𝟙 X := sorry

end StackOver.inertia

namespace StackOver.relativeInertia

variable {X Y : StackOver.{u, v, max w vS, vS} J}

/-- Retaining and then forgetting a relative automorphism agrees with direct forgetting. -/
@[simp, stacks 04Z5 "stack relative-to-absolute inertia forgetful compatibility"]
theorem toInertia.comp_forget (F : X ⟶ Y) :
    toInertia F ≫ inertia.forget X = forget F := sorry

/-- The relative identity section followed by retention is the absolute identity section. -/
@[simp, stacks 04Z5 "stack relative-to-absolute inertia identity compatibility"]
theorem identitySection.comp_toInertia (F : X ⟶ Y) :
    identitySection F ≫ toInertia F = inertia.identitySection X := sorry

end StackOver.relativeInertia

end CategoryTheory
