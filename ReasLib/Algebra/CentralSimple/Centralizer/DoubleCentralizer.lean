/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Centralizer.Simplicity
public import Mathlib.Tactic.CrossRefAttribute

/-! # Double Centralizer Theorem

The double centralizer theorem: if `B` is a simple subalgebra of a finite central simple
`k`-algebra `A`, then `C_A(C_A(B)) = B`.

## Main declarations

- `Subalgebra.centralizer_centralizer_eq` -- the double centralizer recovers `B`.

## References

- [Stacks Project, Tag 074T](https://stacks.math.columbia.edu/tag/074T)

@stack 074T
-/

@[expose] public section

universe u v

namespace Subalgebra

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : Subalgebra k A)
variable [IsSimpleRing B]

local notation "C" => centralizer k (B : Set A)

omit [IsSimpleRing B] in
/-- If two centralizer dimension formulas inside `A` share the same
positive factor `[C : k]`, then their remaining factors agree. -/
private theorem finrank_eq_of_centralizer_dimension_formulas
    (hB : Module.finrank k A = Module.finrank k B * Module.finrank k C)
    (hC :
      Module.finrank k A =
        Module.finrank k C * Module.finrank k (centralizer k (C : Set A))) :
    Module.finrank k B = Module.finrank k (centralizer k (C : Set A)) := by
  -- Move the common factor `[C : k]` to the left in both formulas so cancellation applies.
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos <| by
    calc
      Module.finrank k C * Module.finrank k B = Module.finrank k A := by
        rw [Nat.mul_comm, hB]
      _ = Module.finrank k C * Module.finrank k (centralizer k (C : Set A)) := hC

-- Proof sketch: apply the dimension formula again to the inclusion `C ⊆ A`, where `C` is the
-- centralizer of `B`, to show that the centralizer of `C` has the same `k`-dimension as `B`;
-- combine this with the obvious inclusion `B ≤ C_A(C)` to deduce equality.
/-- If `C` is the centralizer of a simple subalgebra `B ⊆ A`, then the
centralizer of `C` in `A` is exactly `B`. -/
@[stacks 074T]
theorem centralizer_centralizer_eq :
    centralizer k (C : Set A) = B := by
  letI : IsSimpleRing C := isSimpleRing_centralizer (k := k) (A := A) (B := B)
  have hB :
      Module.finrank k A = Module.finrank k B * Module.finrank k C :=
    finrank_centralizer (k := k) (A := A) (B := B)
  have hC :
      Module.finrank k A =
        Module.finrank k C * Module.finrank k (centralizer k (C : Set A)) :=
    finrank_centralizer (k := k) (A := A) (B := C)
  have hfin :
      Module.finrank k B = Module.finrank k (centralizer k (C : Set A)) :=
    finrank_eq_of_centralizer_dimension_formulas (k := k) (A := A) (B := B) hB hC
  have hle : B ≤ centralizer k (C : Set A) :=
    Subalgebra.le_centralizer_centralizer (R := k) (s := B)
  -- The bicentralizer contains `B`, and the dimension computation shows this inclusion is an equality.
  exact (Subalgebra.eq_of_le_of_finrank_eq hle hfin).symm

end

end Subalgebra

end
