/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Setoids.AbsoluteMaps
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Sets.RelativeMaps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolute inertia maps for stacks in sets

Forgetful and identity-section morphisms, their direct setoid-stack computation rules, and the
resulting objectwise equivalence.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets

/-- Forget the selected automorphism from absolute inertia of a stack in sets. -/
@[stacks 042H "set-stack inertia structure map"]
def inertia.forget (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    inertia X ⟶ X :=
  Hom.lift (StackOver.Setoids.inertia.forget X.toSetoids)

/-- The underlying setoid-stack morphism is neutral inertia forgetting. -/
@[simp]
theorem inertia.forget.hom
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (inertia.forget X).hom =
      StackOver.Setoids.inertia.forget X.toSetoids := sorry

/-- Forgetting to set-fibred categories recovers neutral inertia forgetting directly. -/
@[simp, stacks 042H "underlying set-fibred inertia forgetful morphism"]
theorem inertia.forget.toSets
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    Hom.toSetsMor (inertia.forget X) =
      FiberedCategoryOver.Sets.Inertia.forget X.toSets := sorry

/-- The based functor underlying inertia forgetting is the neutral forgetful map. -/
@[simp]
theorem inertia.forget.toBasedFunctor
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    Hom.toBasedFunctor (inertia.forget X) =
      BasedCategory.Inertia.forget X.toBasedCategory := sorry

/-- Equip every object of a stack in sets with its identity automorphism. -/
@[stacks 04Z3 "set-stack inertia neutral section"]
def inertia.identitySection
    (X : StackOver.Sets.{u, v, max w vS, vS} J) : X ⟶ inertia X :=
  Hom.lift (StackOver.Setoids.inertia.identitySection X.toSetoids)

/-- The underlying setoid-stack morphism is the neutral identity section. -/
@[simp]
theorem inertia.identitySection.hom
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (inertia.identitySection X).hom =
      StackOver.Setoids.inertia.identitySection X.toSetoids := sorry

/-- Forgetting to set-fibred categories recovers the neutral identity section directly. -/
@[simp, stacks 04Z3 "underlying set-fibred inertia identity section"]
theorem inertia.identitySection.toSets
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    Hom.toSetsMor (inertia.identitySection X) =
      FiberedCategoryOver.Sets.Inertia.identitySection X.toSets := sorry

/-- The based functor underlying the inertia identity section is the neutral section. -/
@[simp]
theorem inertia.identitySection.toBasedFunctor
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    Hom.toBasedFunctor (inertia.identitySection X) =
      BasedCategory.Inertia.identitySection X.toBasedCategory := sorry

/-- The inertia identity section is a right inverse to forgetting. -/
@[simp]
theorem inertia.identitySection.comp_forget
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    inertia.identitySection X ≫ inertia.forget X = 𝟙 X := sorry

/-- Discrete fibres make inertia forgetting a left inverse to the identity section. -/
@[simp]
theorem inertia.forget.comp_identitySection
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    inertia.forget X ≫ inertia.identitySection X = 𝟙 (inertia X) := sorry

/-- Absolute inertia of a stack in sets is canonically equivalent to the original stack. -/
@[stacks 04Z3 "set-stack inertia equivalence"]
def inertia.forget.equivalence
    (X : StackOver.Sets.{u, v, max w vS, vS} J) : inertia X ≌ X :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (StackOver.Setoids.inertia.forget.equivalence X.toSetoids)

/-- The forward morphism of the inertia equivalence forgets the selected automorphism. -/
@[simp]
theorem inertia.forget.equivalence.hom
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (inertia.forget.equivalence X).hom = inertia.forget X := sorry

/-- The inverse morphism of the inertia equivalence is the identity section. -/
@[simp]
theorem inertia.forget.equivalence.inv
    (X : StackOver.Sets.{u, v, max w vS, vS} J) :
    (inertia.forget.equivalence X).inv = inertia.identitySection X := sorry

/-- Retaining and then forgetting a relative automorphism agrees with direct forgetting. -/
@[simp]
theorem relativeInertia.toInertia.comp_forget
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    relativeInertia.toInertia F ≫ inertia.forget X =
      relativeInertia.forget F := sorry

/-- The relative identity section followed by retention is the absolute identity section. -/
@[simp]
theorem relativeInertia.identitySection.comp_toInertia
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    relativeInertia.identitySection F ≫ relativeInertia.toInertia F =
      inertia.identitySection X := sorry

end StackOver.Sets

end CategoryTheory
