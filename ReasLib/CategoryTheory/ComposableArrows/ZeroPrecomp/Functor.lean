module

public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp.Map
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial Zero Precomposition

Adjoining a fixed number of zero morphisms is a functor on finite composable
rows.  This packages the object and morphism APIs from `ZeroPrecomp` and
`ZeroPrecomp.Map` for direct use in downstream constructions.
-/

open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.ComposableArrows

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasZeroObject D]

namespace zeroPrecomp

/-- The functor adjoining `m` zero morphisms to the left of a finite row. -/
@[stacks 0D81 "functor adjoining zero morphisms to a composable row"]
noncomputable def functor {n : ℕ} (m : ℕ) :
    ComposableArrows D n ⥤ ComposableArrows D (n + m) where
  obj X := X.zeroPrecomp m
  map f := map f m
  map_id := fun X ↦ map_id X m
  map_comp := fun f g ↦ map_comp f g m

/-- The object action of the zero-precomposition functor is
`ComposableArrows.zeroPrecomp`. -/
@[simp]
theorem functor_obj {n : ℕ} (m : ℕ) (X : ComposableArrows D n) :
    (functor (D := D) m).obj X = X.zeroPrecomp m := sorry

/-- The morphism action of the zero-precomposition functor is
`ComposableArrows.zeroPrecomp.map`. -/
@[simp]
theorem functor_map {n : ℕ} (m : ℕ) {X Y : ComposableArrows D n}
    (f : X ⟶ Y) :
    (functor (D := D) m).map f = map f m := sorry

/-- Adjoining no zero morphisms gives the identity functor. -/
theorem functor_zero (n : ℕ) :
    functor (D := D) (n := n) 0 = 𝟭 (ComposableArrows D n) := sorry

/-- Forgetting the newest zero component after successor zero precomposition
recovers the preceding zero-precomposition functor. -/
@[simp]
theorem functor_succ_comp_δ₀ {n : ℕ} (m : ℕ) :
    functor (D := D) (n := n) (m + 1) ⋙ δ₀Functor =
      functor (D := D) (n := n) m := sorry

end zeroPrecomp

end CategoryTheory.ComposableArrows
