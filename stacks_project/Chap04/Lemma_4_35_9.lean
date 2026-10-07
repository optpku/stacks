module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Groupoids.FiberwiseEquivalence

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

namespace FiberedCategoryOver.Groupoids

variable (F : X ⟶ Y)

/- Lemma 4.35.9 (1): a functor over `C` between categories fibred in groupoids is faithful if and
only if every induced fibre functor is faithful. -/
@[stacks 003Z "(1)"]
#check (faithful_iff_fiberwise F :
  (toBasedFunctor F).Faithful ↔
    ∀ U : C, (fiberFunctor F U).Faithful)

/- Lemma 4.35.9 (2): it is fully faithful if and only if every induced fibre functor is fully
faithful. -/
@[stacks 003Z "(2)"]
#check (fullyFaithful_iff_fiberwise F :
  Nonempty (toBasedFunctor F).FullyFaithful ↔
    ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful)

/- Lemma 4.35.9 (3): its total functor is an equivalence if and only if every induced fibre
functor is an equivalence. -/
@[stacks 003Z "(3)"]
#check (isEquivalence_iff_fiberwise F :
  (toFunctor F).IsEquivalence ↔
    ∀ U : C, (fiberFunctor F U).IsEquivalence)

/- Lemma 4.35.9 (4): an equivalence of total categories upgrades to a bicategorical equivalence
over `C` whose forward `1`-morphism is the supplied morphism. -/
@[stacks 003Z "(4)"]
#check (fun (hF : (toFunctor F).IsEquivalence) ↦
  toFunctor.existsEquivalence F hF :
  (toFunctor F).IsEquivalence → ∃ e : X ≌ Y, e.hom = F)

end FiberedCategoryOver.Groupoids

end CategoryTheory
