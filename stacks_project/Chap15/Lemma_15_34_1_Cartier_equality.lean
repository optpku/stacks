/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.Field.Cartier

/-!
# Cartier equality

This file recalls the canonical field-cotangent formulation of Cartier's
equality.

@stack 07E1
-/

@[expose] public section

open scoped KaehlerDifferential

noncomputable section

universe u v

namespace Algebra

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Algebra.FiniteType k K]

/- Lemma 15.34.1 (Cartier equality) (1), tag `07E1`:
`Omega[K / k]` is finite-dimensional over `K`. -/
#synth FiniteDimensional K Ω[K⁄k]

/- Lemma 15.34.1 (Cartier equality) (2), tag `07E1`:
`H1Cotangent k K` is finite-dimensional over `K`. -/
#synth FiniteDimensional K (H1Cotangent k K)

/- Lemma 15.34.1 (Cartier equality) (3), tag `07E1`:
the transcendence degree is the cotangent Euler characteristic. -/
@[stacks 07E1 "Lemma 15.34.1 (Cartier equality)"]
#check @Algebra.cartier_equality

end Algebra
