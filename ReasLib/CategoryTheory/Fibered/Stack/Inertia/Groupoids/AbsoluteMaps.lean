module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Groupoids.RelativeMaps
import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolute inertia maps of groupoid stacks

The absolute forgetful map and identity section, their direct computations, and the criterion
characterizing when inertia forgetting is an equivalence.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.inertia

/-- Forget the selected automorphism from bundled absolute inertia. -/
@[stacks 042H "groupoid-stack inertia structure map"]
def forget (X : StackOver.Groupoids.{u, v, max w vS, vS} J) : inertia X ⟶ X :=
  Hom.lift (FiberedCategoryOver.Groupoids.Inertia.forget X.toGroupoids)

/-- The underlying groupoid-fibred morphism is neutral inertia forgetting. -/
@[simp, stacks 042H "underlying groupoid-stack inertia forgetful morphism"]
theorem forget.hom (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    (forget X).hom = FiberedCategoryOver.Groupoids.Inertia.forget X.toGroupoids := sorry

/-- The underlying based functor is the neutral inertia-forgetful map. -/
@[simp]
theorem forget.toBasedFunctor (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    Hom.toBasedFunctor (forget X) =
      BasedCategory.Inertia.forget X.toBasedCategory := sorry

/-- Equip every object of a groupoid stack with its identity automorphism. -/
@[stacks 04Z3 "groupoid-stack inertia neutral section"]
def identitySection
    (X : StackOver.Groupoids.{u, v, max w vS, vS} J) : X ⟶ inertia X :=
  Hom.lift (FiberedCategoryOver.Groupoids.Inertia.identitySection X.toGroupoids)

/-- The underlying groupoid-fibred morphism is the canonical neutral identity section. -/
@[simp, stacks 04Z3 "underlying absolute inertia identity section"]
theorem identitySection.hom
    (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    (identitySection X).hom =
      FiberedCategoryOver.Groupoids.Inertia.identitySection X.toGroupoids := sorry

/-- The based functor underlying the stack-level identity section is the neutral based
identity section. -/
@[simp, stacks 04Z3 "based absolute inertia identity section"]
theorem identitySection.toBasedFunctor
    (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    Hom.toBasedFunctor (identitySection X) =
      BasedCategory.Inertia.identitySection X.toBasedCategory := sorry

/-- The groupoid-stack inertia identity section is a right inverse to inertia forgetting. -/
@[simp, stacks 04Z3 "groupoid-stack inertia identity-section round trip"]
theorem identitySection.comp_forget
    (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    identitySection X ≫ forget X = 𝟙 X := sorry

/-- The neutral based inertia-forgetful map is an equivalence exactly when the stack is fibred
in setoids. -/
@[stacks 04ZM "universe-polymorphic absolute inertia criterion"]
theorem basedForget.isEquivalence_iff
    (X : StackOver.Groupoids.{u, v, w, vS} J) :
    (BasedCategory.Inertia.forget X.toBasedCategory).IsEquivalence ↔
      IsStack.InSetoids J X.p := sorry

/-- The inertia-forgetful morphism is an equivalence exactly for stacks in setoids. -/
@[stacks 04ZM "absolute inertia criterion for stacks in setoids"]
theorem forget.isEquivalence_iff
    (X : StackOver.Groupoids.{u, v, max w vS, vS} J) :
    Hom.IsEquivalence (forget X) ↔ IsStack.InSetoids J X.p := sorry

end StackOver.Groupoids.inertia

namespace StackOver.Groupoids.relativeInertia

variable {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J}

/-- Retaining and then forgetting a relative automorphism agrees with direct forgetting. -/
@[simp, stacks 04Z5 "groupoid-stack relative-to-absolute inertia forgetful compatibility"]
theorem toInertia.comp_forget (F : X ⟶ Y) :
    toInertia F ≫ inertia.forget X = forget F := sorry

/-- The relative identity section followed by retention is the absolute identity section. -/
@[simp, stacks 04Z5 "groupoid-stack relative-to-absolute inertia identity compatibility"]
theorem identitySection.comp_toInertia (F : X ⟶ Y) :
    identitySection F ≫ toInertia F = inertia.identitySection X := sorry

end StackOver.Groupoids.relativeInertia

end CategoryTheory
