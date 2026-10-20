/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Elementary consequences of algebra epimorphisms

This leaf owns the universal mapping and base-change consequences of
`Algebra.IsEpi`. It is independent of a chosen presentation, fiber, or
localization, so downstream files can import it directly.

@stack 04VQ
@stack 04VU
@stack 04VV
@stack 04W0
-/

open scoped TensorProduct

universe u v w

namespace Algebra.IsEpi

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Two `R`-algebra maps out of an epic `R`-algebra agree. -/
theorem algHom_ext {T : Type w} [CommSemiring T] [Algebra R T] [Algebra.IsEpi R S]
    (f g : S →ₐ[R] T) :
    f = g := sorry

/-- Stacks Lemma 10.107.3, tag `04VQ`: arbitrary tensor-product base change of an epic algebra is
epic. -/
@[stacks 04VQ "epimorphism stable under tensor base change"]
theorem baseChange {R' : Type w} [CommSemiring R'] [Algebra R R'] [Algebra.IsEpi R S] :
    Algebra.IsEpi R' (R' ⊗[R] S) := sorry

end Algebra.IsEpi

namespace Algebra.IsEpi

section FaithfullyFlat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Stacks Lemma 10.107.7, tag `04VU`: a faithfully flat epic algebra map is bijective. -/
@[stacks 04VU "faithfully flat algebra epimorphism"]
theorem faithfullyFlat_bijective [Algebra.IsEpi R S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    Function.Bijective (algebraMap R S) := sorry

end FaithfullyFlat

section Field

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- Stacks Lemma 10.107.8, tag `04VV`: an epic algebra over a field is either the zero ring or
the base field. -/
@[stacks 04VV "epimorphism out of a field"]
theorem subsingleton_or_nonempty_algEquiv [Algebra.IsEpi k S] :
    Subsingleton S ∨ Nonempty (k ≃ₐ[k] S) := sorry

end Field

section Cardinality

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Stacks Lemma 10.107.13, tag `04W0`: the target of an epimorphism of commutative rings has
cardinality at most that of its source. -/
@[stacks 04W0 "cardinality bound for an epic algebra"]
theorem cardinalMk_le [Algebra.IsEpi R S] :
    Cardinal.lift.{u} (Cardinal.mk S) ≤ Cardinal.lift.{v} (Cardinal.mk R) := sorry

end Cardinality

end Algebra.IsEpi
