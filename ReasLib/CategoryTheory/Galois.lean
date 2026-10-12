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

open Limits

namespace PreGaloisCategory

/-- A fiber functor on a Galois category is faithful. -/
theorem galoisCategory_fiberFunctor_faithful {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] : F.Faithful := sorry

/-- A morphism is monic exactly when its image under a fiber functor is injective. -/
theorem fiberFunctor_mono_iff_injective {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective (F.map f) := sorry

/-- A morphism is epic exactly when its image under a fiber functor is surjective. -/
theorem fiberFunctor_epi_iff_surjective {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective (F.map f) := sorry

/-- An object is initial exactly when its fiber is empty. -/
theorem galoisCategory_initial_iff_fiber_empty {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (A : C) :
    Nonempty (IsInitial A) ↔ IsEmpty (F.obj A) := sorry

/-- An object is terminal exactly when its fiber has exactly one element. -/
theorem fiberFunctor_terminal_iff_singleton {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (Z : C) :
    Nonempty (IsTerminal Z) ↔ ∃ z : F.obj Z, ∀ y : F.obj Z, y = z := sorry

/-- Every morphism between connected objects is epic. -/
theorem epi_of_connected_objects {C : Type u} [Category.{v} C] [GaloisCategory C]
    {X Y : C} [IsConnected X] [IsConnected Y] (f : X ⟶ Y) : Epi f := sorry

/-- Evaluation at one point of a connected object is injective on morphisms. -/
theorem fiberFunctor_hom_ext_of_isConnected {C : Type u} [Category.{v} C]
    [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] {X Y : C}
    [IsConnected X] (a b : X ⟶ Y) (x : F.obj X) (h : F.map a x = F.map b x) : a = b := sorry

/-- A morphism between finite coproducts of connected objects is componentwise. -/
theorem coproduct_map_of_connected_components {C : Type u} [Category.{v} C]
    [GaloisCategory C] (n m : ℕ) (X₀ Y₀ : C) (X : Fin n → C) (Y : Fin m → C)
    (hX : X₀ ≅ ∐ X) (hY : Y₀ ≅ ∐ Y) (f : X₀ ⟶ Y₀)
    [∀ i, IsConnected (X i)] [∀ j, IsConnected (Y j)] :
    ∃ (α : Fin n → Fin m) (g : ∀ i, X i ⟶ Y (α i)),
      ∀ i, Sigma.ι X i ≫ hX.inv ≫ f ≫ hY.hom = g i ≫ Sigma.ι Y (α i) := sorry

end PreGaloisCategory

end CategoryTheory

end
