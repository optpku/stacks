/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.DimensionFormula

@[expose] public section

/-!
# Height-one primes in a finite fraction-field extension

@stack 02MA

The fraction-field algebra action is selected by
`FractionRing.algebraOfInjective`.  It remains scoped inside the finiteness
hypothesis because this action depends on the chosen injective map and should
not be installed globally.
-/

noncomputable section

universe u v

namespace Ideal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsDomain A] [IsDomain B] [Algebra A B]

/-- Lemma 10.113.2 (1), tag 02MA: only finitely many primes of the target lie
over a height-one prime when the induced fraction-field extension is finite. -/
@[stacks 02MA "(1), finite primes over a height-one prime"]
theorem finite_primesOver_of_fractionRing_finite
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    (hfinite :
      letI : Algebra (FractionRing A) (FractionRing B) :=
        FractionRing.algebraOfInjective (R := A) (S := B) hinj
      FiniteDimensional (FractionRing A) (FractionRing B))
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    Finite (p.primesOver B) := sorry

/-- Lemma 10.113.2 (2), tag 02MA: every target prime over the height-one
source prime also has height one. -/
@[stacks 02MA "(2), height of primes over a height-one prime"]
theorem height_eq_one_of_primesOver_of_fractionRing_finite
    [IsNoetherianRing A] [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B))
    (hfinite :
      letI : Algebra (FractionRing A) (FractionRing B) :=
        FractionRing.algebraOfInjective (R := A) (S := B) hinj
      FiniteDimensional (FractionRing A) (FractionRing B))
    {p : Ideal A} [p.IsPrime] (hp : p.height = 1) (q : p.primesOver B) :
    q.1.height = 1 := sorry

end Ideal
