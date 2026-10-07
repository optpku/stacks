module

public import ReasLib.CategoryTheory.ComposableArrows.Complex
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Zero Precomposition of Composable Rows

This leaf owns the explicit operation of adjoining finitely many zero arrows
to the left of a finite composable row and its basic complexness API.
-/

open scoped ZeroObject

universe v u

namespace CategoryTheory

namespace ComposableArrows

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroMorphisms D] [Limits.HasZeroObject D]

/-- Prefix a finite row by `m` zero morphisms. -/
@[stacks 0D81]
noncomputable def zeroPrecomp {n : ℕ} (X : ComposableArrows D n) :
    (m : ℕ) → ComposableArrows D (n + m)
  | 0 => X
  | m + 1 => (zeroPrecomp X m).precomp (0 : (0 : D) ⟶ (zeroPrecomp X m).left)

/-- Zero precomposition by no arrows is the original row. -/
@[stacks 0D81, simp]
theorem zeroPrecomp_zero {n : ℕ} (X : ComposableArrows D n) :
    X.zeroPrecomp 0 = X := rfl

/-- Zero precomposition by a successor number of arrows is one further left precomposition. -/
@[stacks 0D81, simp]
theorem zeroPrecomp_succ {n : ℕ} (X : ComposableArrows D n) (m : ℕ) :
    X.zeroPrecomp (m + 1) =
      (X.zeroPrecomp m).precomp (0 : (0 : D) ⟶ (X.zeroPrecomp m).left) := rfl

/-- Removing the newly adjoined leftmost arrow from a successor zero precomposition recovers
the preceding zero precomposition. -/
@[stacks 0D81, simp]
theorem zeroPrecomp_succ_δ₀ {n : ℕ} (X : ComposableArrows D n) (m : ℕ) :
    (X.zeroPrecomp (m + 1)).δ₀ = X.zeroPrecomp m := sorry

namespace IsComplex

/-- Zero precomposition of a complex finite row remains complex. -/
@[stacks 0D81]
theorem zeroPrecomp {n : ℕ} {X : ComposableArrows D n} (hX : X.IsComplex) (m : ℕ) :
    (X.zeroPrecomp m).IsComplex := sorry

end IsComplex

end

end ComposableArrows

end CategoryTheory
