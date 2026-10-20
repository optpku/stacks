module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor
public import ReasLib.Algebra.Category.ModuleCat.Free.Adjunction
public import ReasLib.CategoryTheory.NatTrans.Arrow
import StacksCheckRecall

/-!
# Definition 15.55.5

@stack 01D9

For an arbitrary ring `R`, character duality sends left `R`-modules contravariantly to left
`Rᵐᵒᵖ`-modules.  The free-forget counit packages the functorial free presentation
`F(M) ⟶ M`; its arrow functor records these maps as objects of `Arrow (ModuleCat R)`.
-/

@[expose] public section

open CategoryTheory

universe u v

/- Definition 15.55.5 (1): character duality over a ring is the canonical contravariant functor
to modules over the opposite ring. -/
@[stacks 01D9 "Definition 15.55.5 (1): character-module functor"]
#check fun (R : Type u) [Ring R] ↦
  (CharacterModule.opFunctor R :
    (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ)

/- Definition 15.55.5 (2): the counit of the free-forget adjunction is the functorial
surjection from the free module on the underlying set to the original module. -/
@[stacks 01D9 "Definition 15.55.5 (2): free-module counit"]
#check fun (R : Type u) [Ring R] ↦
  (ModuleCat.Free.counit R :
    CategoryTheory.forget (ModuleCat.{max u v} R) ⋙
      ModuleCat.Free.functor R ⟶ 𝟭 (ModuleCat.{max u v} R))

@[stacks 01D9 "Definition 15.55.5 (2): free-presentation arrow functor"]
#check fun (R : Type u) [Ring R] ↦
  (ModuleCat.Free.counit R).arrowFunctor

#check @ModuleCat.Free.counit_mk

/- For a commutative ring, the opposite-ring action identifies with the usual character-module
endofunctor. -/
#check fun (R : Type u) [CommRing R] ↦
  (CharacterModule.functor R :
    (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{max u v} R)
