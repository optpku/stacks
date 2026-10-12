/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Flat
import StacksCheckRecall

universe u

/- Lemma 35.4.24: if an `R`-module `M` is flat, then its character module
`CharacterModule.moduleObj R M` is injective. -/
@[stacks 08XC] #check (CharacterModule.injective_of_flat :
  ∀ (R : Type u) [CommRing R] (M : ModuleCat.{u} R) [Module.Flat R M],
    Module.Injective R (CharacterModule.moduleObj R M))
