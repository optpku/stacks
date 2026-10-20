/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.SpanRankOperations

@[expose] public section

open TensorProduct

universe u v w

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Over a Noetherian local ring, the minimal number of generators of the tensor product
of two finite modules is the product of their minimal numbers of generators. -/
theorem spanFinrank_tensorProduct
    {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A M] [Module.Finite A N] :
    (⊤ : Submodule A (M ⊗[A] N)).spanFinrank =
      (⊤ : Submodule A M).spanFinrank * (⊤ : Submodule A N).spanFinrank := sorry

/-- If an ideal of a Noetherian local ring needs more than one generator, its square
needs strictly fewer generators than the square of its minimal number of generators. -/
theorem spanFinrank_sq_lt {I : Ideal A} (hI : 1 < I.spanFinrank) :
    (I ^ 2).spanFinrank < I.spanFinrank ^ 2 := sorry

end IsLocalRing
