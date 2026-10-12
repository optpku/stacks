/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat integral algebras over a Zariski pair

@stack 0ELZ
-/

@[expose] public section

universe u v

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 15.10.3: a flat integral finitely presented algebra over a Zariski pair is trivial when
its reduction modulo the distinguished ideal is trivial. -/
@[stacks 0ELZ "flat integral algebra over a Zariski pair"]
theorem bijective_algebraMap_of_zariskiPair
    (I : Ideal A) [Module.Flat A B] [Algebra.IsIntegral A B] [Algebra.FinitePresentation A B]
    (hI : I ≤ Ring.jacobson A)
    (hquot : (A ⧸ I) ≃ₐ[A ⧸ I] (B ⧸ I.map (algebraMap A B))) :
    Function.Bijective (algebraMap A B) := sorry

end Algebra
