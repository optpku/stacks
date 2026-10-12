/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom

@[expose] public section

open CategoryTheory

universe u

#check (CharacterModule.TensorHom.iso :
  ∀ (R : Type u) [CommRing R],
    CharacterModule.TensorHom.tensorFunctor R ≅
      CharacterModule.TensorHom.homFunctor R)
