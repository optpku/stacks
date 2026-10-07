module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.TensorHom

@[expose] public section

open CategoryTheory

universe u

#check (CharacterModule.TensorHom.iso :
  ∀ (R : Type u) [CommRing R],
    CharacterModule.TensorHom.tensorFunctor R ≅
      CharacterModule.TensorHom.homFunctor R)
