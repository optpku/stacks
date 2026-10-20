/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

@[expose] public section

/-!
# Maximal points over an ideal

This leaf owns the maximal-spectrum version of a prime fiber.  Mathlib's
`Ideal.primesOver` indexes all prime ideals over an ideal; `MaximalSpectrum.over`
is the corresponding subtype when a downstream construction genuinely ranges
over closed points.
-/

namespace MaximalSpectrum

universe u v

/-- The maximal ideals of `S` lying over the ideal `p` of `R`. -/
abbrev over {R : Type u} [CommRing R] (p : Ideal R)
    (S : Type v) [CommRing S] [Algebra R S] :=
  { m : MaximalSpectrum S // m.asIdeal.LiesOver p }

/-- A point of `MaximalSpectrum.over p S` carries its defining lying-over relation. -/
instance instLiesOverOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (m : over p S) :
    m.1.asIdeal.LiesOver p :=
  m.2

/-- A maximal point over `p` is in particular a prime point over `p`. -/
def toPrimesOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (m : over p S) : p.primesOver S :=
  ⟨m.1.asIdeal, ⟨m.1.isMaximal.isPrime, m.2⟩⟩

/-- The canonical map from maximal points over an ideal to all prime points over that ideal is
injective. -/
theorem toPrimesOver_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) :
    Function.Injective (toPrimesOver p : over p S → p.primesOver S) := sorry

/-- A finite prime fiber has a finite maximal subfiber. -/
theorem finite_of_finitePrimesOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [Finite (p.primesOver S)] :
    Finite (over p S) := sorry

/-- Finiteness of a prime fiber automatically restricts to its maximal subfiber. The ideal `p`
is determined by the target type, so this instance does not ask typeclass search to guess a base
ring or a scalar structure. -/
instance instFiniteOfFinitePrimesOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [Finite (p.primesOver S)] :
    Finite (over p S) :=
  finite_of_finitePrimesOver p

/-- If every maximal ideal of `S` lies over `p`, the full maximal spectrum is canonically the
fiber over `p`. -/
def equivOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (h : ∀ m : MaximalSpectrum S, m.asIdeal.LiesOver p) :
    MaximalSpectrum S ≃ over p S where
  toFun m := ⟨m, h m⟩
  invFun m := m.1
  left_inv _ := rfl
  right_inv := sorry

end MaximalSpectrum
