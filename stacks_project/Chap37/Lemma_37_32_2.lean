module

import ReasLib.FieldTheory.Transcendence.LinearForm
import StacksCheckRecall

open scoped BigOperators

universe u v

/- Lemma 37.32.2: if the common zero locus of the first two elements of a finite family
in a finite-type domain over a field has an irreducible component of codimension two, then
some scalar linear combination of the family is jointly algebraically independent with the
rational-function coordinates and the family-weighted linear form. -/
@[stacks 0G4E] #check (AlgebraicIndependent.exists_coefficients :
  ∀
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (n : ℕ) (hn : 2 ≤ n) (g : Fin n → A)
    (hcomponent : ∃ p : Ideal A,
      p ∈ (Ideal.span (Set.range fun i : Fin 2 ↦ g (Fin.castLE hn i))).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A),
    ∃ c : Fin n → k,
      let K := FractionRing A
      let E := FractionRing (MvPolynomial (Fin n) K)
      let x : Fin n → E :=
        fun i ↦ algebraMap (MvPolynomial (Fin n) K) E (MvPolynomial.X i)
      let ℓ : E := ∑ i, algebraMap K E (algebraMap A K (g i)) * x i
      let d : E :=
        algebraMap K E (algebraMap A K (∑ i, algebraMap k A (c i) * g i))
      let independentFamily : Sum (Fin n) (Fin 2) → E :=
        Sum.elim x (Fin.cases ℓ (fun _ ↦ d))
      AlgebraicIndependent k independentFamily)
