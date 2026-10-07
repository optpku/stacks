module

public import ReasLib.RingTheory.Etale.Weakly
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Residue fields of weakly etale maps

A weakly etale map induces algebraic and separable extensions between the
residue fields of lying-over prime ideals.  The residue-field algebra is kept
scoped to the selected pair of primes, since different pairs can produce
competing algebra structures on the same carriers.

@stack 092R
-/

universe u v

namespace Algebra.WeaklyEtale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Lemma 15.105.17 (1): a weakly etale map induces algebraic residue-field
extensions at lying-over prime ideals. -/
@[stacks 092R "Lemma 15.105.17 (1)"]
theorem residueField_isAlgebraic (h : Algebra.WeaklyEtale A B)
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    letI : Algebra p.ResidueField q.1.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q.1
    Algebra.IsAlgebraic p.ResidueField q.1.ResidueField := sorry

/-- Lemma 15.105.17 (2): a weakly etale map induces separable residue-field
extensions at lying-over prime ideals. -/
@[stacks 092R "Lemma 15.105.17 (2)"]
theorem residueField_isSeparable (h : Algebra.WeaklyEtale A B)
    (p : Ideal A) [p.IsPrime] (q : p.primesOver B) :
    letI : Algebra p.ResidueField q.1.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q.1
    Algebra.IsSeparable p.ResidueField q.1.ResidueField := sorry

end Algebra.WeaklyEtale
