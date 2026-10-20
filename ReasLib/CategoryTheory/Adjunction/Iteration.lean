/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Endofunctor.Iteration.Positive
public import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Iterating the unit of an adjunction

This file owns the alternating positive iteration of an adjunction unit.  For `U ⊣ V`, its
components map `V.obj X` into `V` applied to each positive iterate of the comonad endofunctor
`V ⋙ U`.  Algebraic resolutions can specialize this construction without rebuilding an
elementwise recursion.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.IteratedEndofunctor

universe uA uS vA vS

namespace CategoryTheory.Adjunction.unit

variable {A : Type uA} {S : Type uS} [Category.{vA} A] [Category.{vS} S]
variable {U : S ⥤ A} {V : A ⥤ S}

/-- The component of the iterated adjunction unit at `X`, landing in the right-adjoint image of
the corresponding positive comonad iterate. -/
@[stacks 08ND "component of an iterated adjunction unit"]
def iterateApp (adj : U ⊣ V) (X : A) :
    (n : ℕ) → V.obj X ⟶ V.obj (((V ⋙ U) ⁺⦋n⦌).obj X)
  | 0 => adj.unit.app (V.obj X)
  | n + 1 =>
      iterateApp adj X n ≫
        adj.unit.app (V.obj (((V ⋙ U) ⁺⦋n⦌).obj X))

/-- The first iterated-unit component is the unit at the right-adjoint image. -/
@[simp, stacks 08ND "first iterated adjunction-unit component"]
theorem iterateApp_zero (adj : U ⊣ V) (X : A) :
    iterateApp adj X 0 = adj.unit.app (V.obj X) := sorry

/-- A successor iterated-unit component inserts the unit after the preceding positive iterate. -/
@[simp, stacks 08ND "successor iterated adjunction-unit component"]
theorem iterateApp_succ (adj : U ⊣ V) (X : A) (n : ℕ) :
    iterateApp adj X (n + 1) =
      iterateApp adj X n ≫
        adj.unit.app (V.obj (((V ⋙ U) ⁺⦋n⦌).obj X)) := sorry

/-- Iterated adjunction-unit components are natural in the object of the left-hand category. -/
@[stacks 08ND "naturality of iterated adjunction-unit components"]
theorem iterateApp_naturality (adj : U ⊣ V) {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    V.map f ≫ iterateApp adj Y n =
      iterateApp adj X n ≫ V.map (((V ⋙ U) ⁺⦋n⦌).map f) := sorry

/-- The iterated unit, bundled naturally in the object resolved by the adjunction comonad. -/
@[stacks 08ND "iterated unit of an adjunction"]
def iterate (adj : U ⊣ V) (n : ℕ) :
    V ⟶ (V ⋙ U) ⁺⦋n⦌ ⋙ V where
  app X := iterateApp adj X n
  naturality _ _ f := iterateApp_naturality adj f n

/-- The component of the bundled iterated unit is the component-first construction. -/
@[simp, stacks 08ND "component formula for the iterated adjunction unit"]
theorem iterate_app (adj : U ⊣ V) (n : ℕ) (X : A) :
    (iterate adj n).app X = iterateApp adj X n := sorry

end CategoryTheory.Adjunction.unit
