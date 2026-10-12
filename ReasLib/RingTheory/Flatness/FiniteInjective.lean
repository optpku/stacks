/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent along finite injective ring maps

Flatness and projectivity descend from scalar extension along a finite injective map of
Noetherian commutative rings.

@stack 0533
@stack 0H7R
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.Flat

/-- Lemma 15.21.5, Stacks `0533`: let `R → S` be finite and injective with `R` Noetherian. If
the scalar extension `S ⊗[R] M` is flat over `S`, then `M` is flat over `R`. -/
@[stacks 0533 "flatness descent along a finite injective map"]
theorem of_finite_injective_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] M)) :
    Module.Flat R M := sorry

end Module.Flat

namespace Module.Projective

/-- Lemma 15.21.7, Stacks `0H7R`: let `R → S` be finite and injective with `R` Noetherian. If
the scalar extension `S ⊗[R] M` is projective over `S`, then `M` is projective over `R`. -/
@[stacks 0H7R "projectivity descent along a finite injective map"]
theorem of_finite_injective_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    (hinj : Function.Injective (algebraMap R S))
    (hprojective : Module.Projective S (S ⊗[R] M)) :
    Module.Projective R M := sorry

end Module.Projective
