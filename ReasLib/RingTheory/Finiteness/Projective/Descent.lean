/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.FaithfullyFlat.Projective
public import ReasLib.RingTheory.Finiteness.Projective.BaseChange

/-!
# Faithfully Flat Descent of Finite Projective Modules

This leaf combines the independent finite and projective faithfully-flat
descent APIs into the finite-projective predicate.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.FiniteProjective

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/-- Proposition 10.83.3, tag `058S`: finite projectivity descends from a faithfully flat
scalar extension. -/
@[stacks 058S "faithfully flat descent of finite projective modules"]
theorem of_tensorProduct [Module.FaithfullyFlat R S]
    (hM : Module.FiniteProjective S (S ⊗[R] M)) :
    Module.FiniteProjective R M := sorry

/-- Tag `058S`: finite projectivity is invariant under faithfully flat scalar extension. -/
@[stacks 058S "faithfully flat base change of finite projective modules"]
theorem iff_tensorProduct_of_faithfullyFlat [Module.FaithfullyFlat R S] :
    Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M) := sorry

end Module.FiniteProjective
