/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 35.4.10 (1): the character-module functor is exact. -/
@[stacks 08WR]
#check (CharacterModule.exact :
  ∀ (R : Type u) [CommRing R],
    exactFunctor (ModuleCat.{v} R)ᵒᵖ (ModuleCat.{v} R) (CharacterModule.functor R))

/- Lemma 35.4.10 (2): the character-module functor reflects monomorphisms. -/
@[stacks 08WR]
#check (CharacterModule.instFunctorReflectsMonomorphisms :
  ∀ (R : Type u) [CommRing R],
    (CharacterModule.functor R :
      (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} R).ReflectsMonomorphisms)

/- Lemma 35.4.10 (3): the character-module functor reflects epimorphisms. -/
@[stacks 08WR]
#check (CharacterModule.instFunctorReflectsEpimorphisms :
  ∀ (R : Type u) [CommRing R],
    (CharacterModule.functor R :
      (ModuleCat.{v} R)ᵒᵖ ⥤ ModuleCat.{v} R).ReflectsEpimorphisms)
