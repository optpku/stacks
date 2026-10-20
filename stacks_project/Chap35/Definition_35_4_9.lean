module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Definition 35.4.9: for a commutative ring `R`, character duality is the
contravariant endofunctor sending `M` to `CharacterModule M`. -/
@[stacks 08WQ] #check
  (CharacterModule.functor : ∀ (R : Type u) [CommRing R],
    (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{max u v} R)

#check @CharacterModule.moduleObj
#check @CharacterModule.smul_apply
#check @CharacterModule.dualMap_apply
#check @CharacterModule.functor_map_op
