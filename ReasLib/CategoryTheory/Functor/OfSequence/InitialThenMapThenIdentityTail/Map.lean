/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.OfSequence.InitialThenMapThenIdentityTail.Basic

/-!
# Maps of Stabilizing Sequential Diagrams

This leaf packages the natural transformation of diagrams
`⊥ ⟶ X ⟶ Y ⟶ Y ⟶ ⋯` induced by a commutative square `u ≫ g = f ≫ v`.
The basic construction and its colimit interface are in `Basic`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor.InitialThenMapThenIdentityTail

variable {C : Type u} [Category.{v} C] [HasInitial C]

noncomputable section

/-- The stagewise components induced by a commutative square of input morphisms. -/
def component {X Y X' Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    ∀ n : ℕ, stage X Y n ⟶ stage X' Y' n
  | 0 => 𝟙 _
  | 1 => f
  | _ + 2 => g

/-- The components of a morphism of stabilizing diagrams commute with the successor maps. -/
theorem component_naturality {X Y X' Y' : C}
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ g = f ≫ v) (n : ℕ) :
    (diagram u).map (homOfLE (Nat.le_succ n)) ≫ component f g (n + 1) =
      component f g n ≫ (diagram v).map (homOfLE (Nat.le_succ n)) := sorry

/-- The natural transformation of stabilizing sequential diagrams induced by a commutative
square of morphisms. -/
def map {X Y X' Y' : C}
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ g = f ≫ v) :
    diagram u ⟶ diagram v :=
  NatTrans.ofSequence (component f g) (component_naturality u v f g h)

/-- The component of `map` at a stage is the explicitly specified square component. -/
@[simp]
theorem map_app {X Y X' Y' : C}
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ g = f ≫ v) (n : ℕ) :
    (map u v f g h).app n = component f g n := sorry

/-- At the initial stage, a morphism of stabilizing diagrams is the identity of the initial
object. -/
@[simp]
theorem map_app_zero {X Y X' Y' : C}
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ g = f ≫ v) :
    (map u v f g h).app 0 = 𝟙 _ := sorry

/-- At the `X` stage, a morphism of stabilizing diagrams is the left side of the input square. -/
@[simp]
theorem map_app_one {X Y X' Y' : C}
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ g = f ≫ v) :
    (map u v f g h).app 1 = f := sorry

/-- On the constant tail, a morphism of stabilizing diagrams is the right side of the input
square. -/
@[simp]
theorem map_app_tail {X Y X' Y' : C}
    (u : X ⟶ Y) (v : X' ⟶ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : u ≫ g = f ≫ v) (n : ℕ) :
    (map u v f g h).app (n + 2) = g := sorry

end

end CategoryTheory.Functor.InitialThenMapThenIdentityTail
