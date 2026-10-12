/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Galois.Decomposition

@[expose] public section

universe u v w

namespace CategoryTheory

namespace PreGaloisCategory

/-- Any connected object admits a morphism from a Galois object. -/
theorem exists_galois_object_hom_of_connected {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (X : C)
    [IsConnected X] : ∃ (A : C) (_ : A ⟶ X), IsGalois A := sorry

end PreGaloisCategory

end CategoryTheory

end
