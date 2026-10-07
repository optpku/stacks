module

-- Import decisions:
-- * Definitions 4.35.1 and 4.35.6 are public because the theorem and bundled composition
--   expose their mathematical API in declaration types.
-- * Deferred proof dependencies are intentionally omitted at the statement stage.
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of groupoid-fibred functors

Functorial and bundled closure of categories fibred in groupoids under composition of
projections.
-/

@[expose] public section

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

namespace IsFibered.InGroupoids

namespace Comp

/- The mathematically reusable surface is the closure instance itself. The previous file exposed a
chain of private lemmas about morphisms in standard fibers; those lemmas merely implemented one
proof route and obscured the canonical owner. Keeping the proof route in the declaration docstring
makes the intended use of the mathlib 4.32 APIs explicit without turning proof internals into
public dependencies. -/

/-- Lemma 4.35.14 (Stacks 09WW): if `F : A ⥤ B` and `G : B ⥤ C` are fibred in groupoids, then
`F ⋙ G : A ⥤ C` is fibred in groupoids.

Proof strategy: obtain `(F ⋙ G).IsFibered` from `Functor.isFibered_comp`, then apply
`Functor.IsFibered.InGroupoids.of_isFibered_fibersGroupoid`. A morphism in a standard fiber of `F ⋙ G`
maps under `F` to a morphism in the corresponding fiber of `G`, hence to an isomorphism because
that fiber is a groupoid. Every morphism upstairs is strongly cartesian for `F`; use
`IsStronglyCartesian.isIso_of_base_isIso` to reflect this isomorphism to `A`, and package the
resulting invertibility of every composite-fiber morphism as `IsGroupoid`. -/
@[stacks 09WW "composition of groupoid-fibred functors"]
instance inGroupoids
    (F : A ⥤ B) (G : B ⥤ C)
    [Functor.IsFibered.InGroupoids F] [Functor.IsFibered.InGroupoids G] :
    Functor.IsFibered.InGroupoids (F ⋙ G) := sorry

end Comp
end IsFibered.InGroupoids

end CategoryTheory.Functor

namespace CategoryTheory.FiberedCategoryOver.Groupoids

/-- Compose the projection of a category fibred in groupoids with a second groupoid-fibred
functor. This is the bundled form of `Functor.IsFibered.InGroupoids.Comp.inGroupoids`; it changes the base
without choosing a cleavage or a pseudofunctor presentation. -/
def comp
    {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
    (X : FiberedCategoryOver.Groupoids.{uB, vB, uA, vA} B)
    (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] :
    FiberedCategoryOver.Groupoids.{uC, vC, uA, vA} C :=
  ofFunctor (X.p ⋙ G)

/- The total category and composite projection are explicit. Any `sorryAx` can enter only through
the Prop-valued membership witness supplied by
`Functor.IsFibered.InGroupoids.Comp.inGroupoids`. -/

/-- The total category is unchanged when only the projection base is composed. -/
@[simp]
theorem comp.total
    {B : Type uB} {C : Type uC} [Category.{vB} B] [Category.{vC} C]
    (X : FiberedCategoryOver.Groupoids.{uB, vB, uA, vA} B)
    (G : B ⥤ C) [Functor.IsFibered.InGroupoids G] :
    (comp X G).total = X.total := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
