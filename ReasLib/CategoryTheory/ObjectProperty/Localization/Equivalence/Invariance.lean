/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Calculus

@[expose] public section

/-!
# Localization of Denominator-Invariant Full Subcategories

If an object property is inherited from both ends of every denominator, the inclusion-induced
localizer morphism is localized fully faithful.  This is the model-independent layer: mathlib
then supplies `Functor.Full` and `Functor.Faithful` for every compatible pair of localization
functors, together with `Functor.preimage`, `Functor.map_preimage`, and
`Functor.map_injective`.
-/

universe v u

namespace CategoryTheory

open MorphismProperty ObjectProperty

variable {D : Type u} [Category.{v} D]
  (P : ObjectProperty D) (S : MorphismProperty D)

namespace fullSubcategoryLocalizerMorphism.invariance

/-- denominator invariance makes the inclusion-induced localizer morphism fully
faithful after localization. -/
@[stacks 05SE]
instance isLocalizedFullyFaithful [IsSaturatedMultiplicativeSystem S]
    [P.InheritedFromSource S] [P.InheritedFromTarget S] :
    (fullSubcategoryLocalizerMorphism P S).IsLocalizedFullyFaithful := sorry

end fullSubcategoryLocalizerMorphism.invariance


end CategoryTheory
