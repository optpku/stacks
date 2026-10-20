module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence criterion for cartesian functors between stacks

This module owns the universe-polymorphic form of the fully faithful local equivalence
criterion.  Bundled stack categories expose only specializations of this statement.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

namespace CartesianBasedFunctor

/-- Lemma 8.4.8 (tag 046N), in its heterogeneous cartesian form: a fully faithful cartesian
functor between stacks is an equivalence over the base exactly when it is locally essentially
surjective on fiber objects. -/
@[stacks 046N "heterogeneous cartesian form"]
theorem isEquivalence_iff_locallyEssentiallySurjective
    {J : GrothendieckTopology C} (F : CartesianBasedFunctor p₁ p₂)
    [IsStack.OnSite J p₁] [IsStack.OnSite J p₂]
    (hF : Nonempty F.toFunctor.FullyFaithful) :
    F.toBasedFunctor.IsEquivalence ↔ F.LocallyEssentiallySurjective J := sorry

end CartesianBasedFunctor

end CategoryTheory
