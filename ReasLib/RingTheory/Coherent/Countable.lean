/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Coherent.Products
public import ReasLib.LinearAlgebra.TensorProduct.Pi.Countable

@[expose] public section

universe u

namespace IsCoherentRing

/-- A countable commutative ring is coherent if and only if its natural-number-indexed
product is flat as a module over the ring. -/
@[stacks 0ALB]
theorem iff_piNat_flat {R : Type u} [CommRing R] [Countable R] :
    IsCoherentRing R ↔ Module.Flat R (ℕ → R) := sorry

end IsCoherentRing
