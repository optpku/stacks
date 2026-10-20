module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.FullyFaithful

import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent properties transported by fiberwise equivalences

This leaf transfers prestack and stack conditions across an identity-base indexed functor whose
fiber components are equivalences of categories.
-/

@[expose] public section

universe t uC vC uF vF uG vG

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable (H : IndexedFunctor (𝟭 C) F G)
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- A fiberwise equivalence preserves and reflects the prestack condition for an individual
presieve. -/
@[stacks 026F "fiberwise-equivalence prestack criterion"]
theorem isPrestackFor_iff [H.FiberwiseEquivalence]
    (R : Presieve S) :
    F.IsPrestackFor R ↔ G.IsPrestackFor R := sorry

/-- A fiberwise equivalence preserves and reflects effective descent for an individual
presieve. -/
@[stacks 026F "fiberwise-equivalence stack criterion"]
theorem isStackFor_iff [H.FiberwiseEquivalence]
    (R : Presieve S) :
    F.IsStackFor R ↔ G.IsStackFor R := sorry

/-- A fiberwise equivalence of indexed categories over the identity base preserves and reflects
the prestack condition. -/
@[stacks 026F "fiberwise-equivalence prestack transport"]
theorem isPrestack_iff [H.FiberwiseEquivalence]
    (J : GrothendieckTopology C) :
    F.IsPrestack J ↔ G.IsPrestack J := sorry

/-- A fiberwise equivalence of indexed categories over the identity base preserves and reflects
the stack condition. -/
@[stacks 026F "fiberwise-equivalence stack transport"]
theorem isStack_iff [H.FiberwiseEquivalence]
    (J : GrothendieckTopology C) :
    F.IsStack J ↔ G.IsStack J := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
