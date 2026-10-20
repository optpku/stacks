module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Jacobian
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Example 41.8.2 (1): if the residue-field Jacobian of generators of `I` has full row
rank, then `Spec(MvPolynomial (Fin n) R ⧸ I) ⟶ Spec(R)` is unramified at `q / I`. -/
@[stacks 024Y] #check
  (AlgebraicGeometry.JacobianCriterion.unramifiedAt :
    ∀ {R : Type u} [CommRing R] (n m : ℕ)
      (g : Fin m → MvPolynomial (Fin n) R)
      (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
      (hIq : Ideal.span (Set.range g) ≤ q)
      (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n),
      let I := Ideal.span (Set.range g)
      let qbar : Ideal (MvPolynomial (Fin n) R ⧸ I) :=
        q.map (Ideal.Quotient.mk I)
      let x : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ I) :=
        ⟨qbar, Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩
      let f : Spec (.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ Spec (.of R) :=
        Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))
      f.UnramifiedAt x)

/- Example 41.8.2 (2): full row rank of the `n × m` residue-field Jacobian forces
`n ≤ m`. -/
@[stacks 024Y] #check
  (AlgebraicGeometry.JacobianCriterion.variableCount_le_relationCount :
    ∀ {R : Type u} [CommRing R] (n m : ℕ)
      (g : Fin m → MvPolynomial (Fin n) R)
      (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
      (hIq : Ideal.span (Set.range g) ≤ q)
      (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n),
      n ≤ m)

/- Example 41.8.2 (3): in the square full-rank case, the quotient-spectrum morphism is flat
at the point `q / I`. -/
@[stacks 024Y] #check
  (AlgebraicGeometry.JacobianCriterion.flatAt_of_square :
    ∀ {R : Type u} [CommRing R] (n : ℕ)
      (g : Fin n → MvPolynomial (Fin n) R)
      (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
      (hIq : Ideal.span (Set.range g) ≤ q)
      (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n),
      let I := Ideal.span (Set.range g)
      let qbar : Ideal (MvPolynomial (Fin n) R ⧸ I) :=
        q.map (Ideal.Quotient.mk I)
      let x : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ I) :=
        ⟨qbar, Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩
      let f : Spec (.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ Spec (.of R) :=
        Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))
      f.flatAt x)

/- Example 41.8.2 (4): in the square full-rank case, the quotient-spectrum morphism is étale
at the point `q / I`. -/
@[stacks 024Y] #check
  (AlgebraicGeometry.JacobianCriterion.etaleAt_of_square :
    ∀ {R : Type u} [CommRing R] (n : ℕ)
      (g : Fin n → MvPolynomial (Fin n) R)
      (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
      (hIq : Ideal.span (Set.range g) ≤ q)
      (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n),
      let I := Ideal.span (Set.range g)
      let qbar : Ideal (MvPolynomial (Fin n) R ⧸ I) :=
        q.map (Ideal.Quotient.mk I)
      let x : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ I) :=
        ⟨qbar, Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩
      let f : Spec (.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ Spec (.of R) :=
        Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))
      f.EtaleAt x)
