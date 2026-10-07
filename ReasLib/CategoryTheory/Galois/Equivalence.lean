module

public import Mathlib.CategoryTheory.Galois.Equivalence

@[expose] public section

universe u v w

namespace CategoryTheory.PreGaloisCategory

/-- The functor induced by a fiber functor on a Galois category is an equivalence
with the category of finite continuous actions of its automorphism group. -/
theorem functorToContAction_isEquivalence {C : Type u} [Category.{v} C]
    (F : C ⥤ FintypeCat.{w}) [GaloisCategory C] [FiberFunctor F] :
    (functorToContAction F).IsEquivalence := inferInstance

end CategoryTheory.PreGaloisCategory
