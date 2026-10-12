/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import ReasLib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.LocalRing.Product
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Integral product decompositions over a prime

This file defines finite algebra-product decompositions whose factors are
integral over the base and have selected singleton prime fibers.
-/

universe u v

namespace PrimeSpectrum

/-- A finite algebra-product decomposition whose factors are integral over the
base and have a selected singleton prime fiber over `p`. -/
structure IntegralDecomposition.{u₁, v₁}
    {R : Type u₁} [CommRing R] (p : PrimeSpectrum R)
    (S : Type v₁) [CommRing S] [Algebra R S] where
  /-- The finite product presentation of the algebra. -/
  product : AlgProduct.Decomposition.Finite R S
  /-- Every factor is integral over the base ring. -/
  factorIntegral : ∀ i, Algebra.IsIntegral R (product.factor i)
  /-- The selected prime over `p` in each factor. -/
  factorPoint : ∀ i, p.asIdeal.primesOver (product.factor i)
  /-- The selected prime is the unique prime over `p` in its factor. -/
  factorPrimesOver_eq_singleton :
    ∀ i, p.asIdeal.primesOver (product.factor i) =
      ({(factorPoint i).1} : Set (Ideal (product.factor i)))

namespace IntegralDecomposition

/-- Build an integral decomposition from an explicit finite product and its
integral singleton-fiber data. -/
def of {R : Type u} [CommRing R] (p : PrimeSpectrum R)
    {S : Type v} [CommRing S] [Algebra R S]
    (product : AlgProduct.Decomposition.Finite R S)
    (factorIntegral : ∀ i, Algebra.IsIntegral R (product.factor i))
    (factorPoint : ∀ i, p.asIdeal.primesOver (product.factor i))
    (factorPrimesOver_eq_singleton :
      ∀ i, p.asIdeal.primesOver (product.factor i) =
        ({(factorPoint i).1} : Set (Ideal (product.factor i)))) :
    IntegralDecomposition p S where
  product := product
  factorIntegral := factorIntegral
  factorPoint := factorPoint
  factorPrimesOver_eq_singleton := factorPrimesOver_eq_singleton

/-- The integrality and singleton-fiber conditions carried by an integral
decomposition. -/
theorem spec {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : IntegralDecomposition p S) :
    (∀ i, Algebra.IsIntegral R (D.product.factor i)) ∧
      (∀ i, p.asIdeal.primesOver (D.product.factor i) =
        ({(D.factorPoint i).1} : Set (Ideal (D.product.factor i)))) := sorry

/-- The canonical residue-field map at a selected factor of an integral
decomposition. -/
noncomputable def factorResidueMap
    {R : Type u} [CommRing R] {p : PrimeSpectrum R}
    {S : Type v} [CommRing S] [Algebra R S]
    (D : IntegralDecomposition p S) (i : D.product.index) :
    p.asIdeal.ResidueField →+* (D.factorPoint i).1.ResidueField :=
  Ideal.ResidueField.map p.asIdeal (D.factorPoint i).1
    (algebraMap R (D.product.factor i)) (D.factorPoint i).2.2.over

end IntegralDecomposition

end PrimeSpectrum
