module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Local

/-!
# Local equivalence criteria for stacks in groupoids

This leaf specializes the local equivalence criterion for ordinary stacks to the induced
bicategory of stacks in groupoids. The specialization is kept proposition-valued: consumers do
not need a second public morphism owner merely to compare the two equivalence predicates.

## Main declarations

* `StackOver.Groupoids.Hom.IsEquivalence.iff_locallyEssentiallySurjective` -- the fully
  faithful local equivalence criterion for stacks in groupoids.
-/

@[expose] public section

universe u v

namespace CategoryTheory

namespace StackOver.Groupoids.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Groupoids J}

/-- Lemma 8.4.8 (tag 046N): a fully faithful morphism of stacks in groupoids is an
equivalence over the base exactly when it is locally essentially surjective. -/
@[stacks 046N "groupoid specialization"]
theorem IsEquivalence.iff_locallyEssentiallySurjective
    (F : X ⟶ Y) (h_fullyFaithful : Nonempty (toBasedFunctor F).FullyFaithful) :
    IsEquivalence F ↔ LocallyEssentiallySurjective F := sorry

end StackOver.Groupoids.Hom

end CategoryTheory
