module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Inertia.Section.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithful functors and relative inertia

Faithfulness of a based functor makes its relative-inertia structure map an
equivalence over the base. For a faithful source projection, this applies to
every outgoing based functor through `BasedFunctor.faithfulOfSource`.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace BasedCategory.RelativeInertia.forget

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- Relative-inertia forgetting is an equivalence over the base when the defining based functor
is faithful. -/
@[stacks 04ZM "faithful relative-inertia forgetful equivalence"]
instance isEquivalenceOfFaithful (F : X ⥤ᵇ Y) [F.Faithful] :
    (BasedCategory.RelativeInertia.forget F).IsEquivalence := sorry
/- Proof strategy: use `BasedCategory.RelativeInertia.identitySection F` as the inverse; the
neutral equivalence follows from `CategoryTheory.RelativeInertia.forget.isEquivalenceOfFaithful`,
and both comparison isomorphisms are vertical because their underlying components are identities. -/

end BasedCategory.RelativeInertia.forget

end CategoryTheory
