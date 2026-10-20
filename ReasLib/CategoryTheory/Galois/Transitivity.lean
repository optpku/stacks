/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Galois.Prorepresentability

@[expose] public section

universe u v w

namespace CategoryTheory.PreGaloisCategory.FiberFunctor

/-- Any two points in the fiber of a connected object of a Galois category are related
by a natural automorphism of the fiber functor. -/
theorem exists_aut_app_eq_of_isConnected {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (X : C) [IsConnected X] (x y : F.obj X) :
    ∃ σ : Aut F, σ.hom.app X x = y := sorry

end CategoryTheory.PreGaloisCategory.FiberFunctor

end
