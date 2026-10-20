/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.CountablyGenerated.Operations

/-!
# Base change of countably generated modules

Scalar extension preserves countable generation and internal decompositions into countably
generated submodules. Faithfully flat reflection lives in the corresponding `RingTheory` leaf.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Module.CountablyGenerated

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- Extension of scalars preserves countable generation. -/
theorem baseChange (hM : Module.CountablyGenerated R M) :
    Module.CountablyGenerated S (S ⊗[R] M) := sorry

end Module.CountablyGenerated

namespace Module.CountablyGenerated.IsDirectSum

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- Extension of scalars preserves the canonical independent-supremum decomposition into
countably generated submodules. -/
@[stacks 05A3 "direct-sum decomposition under base change"]
theorem baseChange
    (hM : Module.CountablyGenerated.IsDirectSum.{u, w, x} R M) :
    Module.CountablyGenerated.IsDirectSum.{v, max v w, x} S (S ⊗[R] M) := sorry

end Module.CountablyGenerated.IsDirectSum

namespace Module.IsDirectSumOfCountablyGenerated

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Lemma 10.94.1 (3), tag `05A3`: extension of scalars preserves an internal direct-sum
decomposition into countably generated submodules. -/
@[stacks 05A3 "(3)"]
theorem baseChange
    (hM : Module.IsDirectSumOfCountablyGenerated.{u, w, x} R M) :
    Module.IsDirectSumOfCountablyGenerated.{v, max v w, x} S (S ⊗[R] M) := sorry

end Module.IsDirectSumOfCountablyGenerated
