/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Faithfully flat descent of projective modules

This leaf owns the arbitrary-module form of faithfully flat projective
descent. It is deliberately separate from finite projectivity: no finiteness
assumption belongs to this statement.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.Projective

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/-- Explicit-hypothesis compatibility form of faithfully flat descent of projectivity. -/
@[stacks 05A9 "faithfully flat descent of projective modules"]
theorem of_tensorProduct
    (hff : Module.FaithfullyFlat R S)
    (hM : Module.Projective S (S ⊗[R] M)) :
    Module.Projective R M := sorry

/-- Class-argument form of faithfully flat descent of projectivity. -/
@[stacks 05A9 "faithfully flat descent class API"]
theorem of_baseChange [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] : Module.Projective R M := sorry

/-- Explicit-hypothesis compatibility form of faithfully flat invariance of projectivity. -/
@[stacks 05A9 "faithfully flat base change of projective modules"]
theorem iff_tensorProduct_of_faithfullyFlat
    (hff : Module.FaithfullyFlat R S) :
    Module.Projective R M ↔ Module.Projective S (S ⊗[R] M) := sorry

/-- Class-argument form of faithfully flat invariance of projectivity. -/
@[stacks 05A9 "faithfully flat base change class API"]
theorem iff_baseChange [Module.FaithfullyFlat R S] :
    Module.Projective R M ↔ Module.Projective S (S ⊗[R] M) := sorry

end Module.Projective
