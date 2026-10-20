module

public import ReasLib.CategoryTheory.Fibered.Split
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable (p : S ⥤ C)

/- Lemma 4.36.3: a split fibred category has a pullback choice whose reindexing functors preserve
composition on the nose.  In the explicit cleavage model, that equality forgets the chosen
cartesian arrows, so the reusable formal iff is stated with `Cleavage.IsSplit` instead. -/
@[stacks 02XX]
#check (Functor.IsFibered.Split.iff_existsCleavageIsSplit p :
  Functor.IsFibered.Split p ↔ ∃ χ : p.Cleavage, χ.IsSplit)

/- The strict pullback-functor equality is the reusable consequence of a split cleavage. -/
@[stacks 02XX "strictly compositional pullback-functor consequence"]
#check (Functor.IsFibered.Split.existsCleavageReindexComp (p := p) :
  Functor.IsFibered.Split p → ∃ χ : p.Cleavage, χ.IsStrictlyCompositional)

end CategoryTheory
