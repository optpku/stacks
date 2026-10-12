/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maps Between Zero-Precomposed Rows

Zero precomposition acts on morphisms of finite composable rows.  The
component at each new zero object is the identity, while the remaining tail
is the original row morphism.
-/

open CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

universe v u

namespace CategoryTheory.ComposableArrows

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasZeroObject D]

namespace zeroPrecomp

/-- The zero square used when adjoining one zero morphism to a map of rows. -/
theorem square {n : ℕ} {X Y : ComposableArrows D n}
    (f : X ⟶ Y) :
    (0 : (0 : D) ⟶ X.left) ≫ app' f 0 =
      𝟙 (0 : D) ≫ (0 : (0 : D) ⟶ Y.left) := sorry

/-- A map of finite rows, extended over `m` adjoined zero morphisms. -/
@[stacks 0D81 "map between zero-precomposed composable rows"]
def map {n : ℕ} {X Y : ComposableArrows D n} (f : X ⟶ Y) :
    (m : ℕ) → X.zeroPrecomp m ⟶ Y.zeroPrecomp m
  | 0 => f
  | m + 1 =>
      homMkSucc (𝟙 (0 : D)) (map f m) (square (map f m))

/-- Extending over no zero morphisms leaves a row map unchanged. -/
@[simp]
theorem map_zero {n : ℕ} {X Y : ComposableArrows D n}
    (f : X ⟶ Y) : map f 0 = f := sorry

/-- The first component of a successor zero-precomposition map is the
identity of the zero object. -/
@[simp]
theorem map_succ_app_zero {n : ℕ}
    {X Y : ComposableArrows D n} (f : X ⟶ Y) (m : ℕ) :
    app' (map f (m + 1)) 0 = 𝟙 (0 : D) := sorry

/-- Away from the newly adjoined zero object, a successor
zero-precomposition map is the preceding extension. -/
@[simp]
theorem map_succ_app_succ {n : ℕ}
    {X Y : ComposableArrows D n} (f : X ⟶ Y) (m i : ℕ)
    (hi : i ≤ n + m) :
    app' (map f (m + 1)) (i + 1) = app' (map f m) i := sorry

/-- Removing the newest zero component from an extended map recovers the
preceding extension. -/
@[simp]
theorem map_succ_δ₀ {n : ℕ}
    {X Y : ComposableArrows D n} (f : X ⟶ Y) (m : ℕ) :
    δ₀Functor.map (map f (m + 1)) = map f m := sorry

/-- Zero precomposition preserves identity maps. -/
@[simp]
theorem map_id {n : ℕ} (X : ComposableArrows D n) (m : ℕ) :
    map (𝟙 X) m = 𝟙 (X.zeroPrecomp m) := sorry

/-- Zero precomposition preserves composition of row maps. -/
@[simp]
theorem map_comp {n : ℕ} {X Y Z : ComposableArrows D n}
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    map (f ≫ g) m = map f m ≫ map g m := sorry

end zeroPrecomp

end CategoryTheory.ComposableArrows
