/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.LocalEquivalence

/-!
# Constructing stackifications from local equivalences

The canonical stackification predicate already stores a local equivalence and a target stack.
This leaf provides explicit-proof constructors at the heterogeneous and fixed-universe levels,
so downstream theorem data need not be installed as temporary instances.
-/

@[expose] public section

universe u v w vS uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} [p₁.IsFibered]

/-- A heterogeneous local equivalence into a stack is a stackification. -/
@[stacks 02ZN "construct a stackification from the two local conditions"]
theorem IsLocalEquivalence.isStackification
    {J : GrothendieckTopology C} {F : CartesianBasedFunctor p₁ p₂}
    [IsStack.OnSite J p₂] (hF : IsLocalEquivalence J F) :
    IsStackification J F := sorry

end CartesianBasedFunctor

namespace FiberedCategoryOver.Hom

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The fixed-universe specialization of the heterogeneous local-equivalence criterion for
stackification. -/
@[stacks 02ZN "fixed-universe stackification constructor"]
theorem IsLocalEquivalence.isStackification
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : IsLocalEquivalence J F) [IsStack.OnSite J Y.p] :
    IsStackification J F := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
