module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
public import ReasLib.RingTheory.MvPolynomial.Jacobian
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Jacobian criteria for quotient-spectrum morphisms

This file relates full rank of a residue-field Jacobian to pointwise
unramifiedness and, in the square case, flatness and étaleness.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.JacobianCriterion

/-- Full row rank of the residue-field Jacobian of generators of `I` implies that
`Spec(MvPolynomial (Fin n) R ⧸ I) ⟶ Spec(R)` is unramified at `q / I`. -/
theorem unramifiedAt {R : Type u} [CommRing R] (n m : ℕ)
    (g : Fin m → MvPolynomial (Fin n) R)
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hIq : Ideal.span (Set.range g) ≤ q)
    (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n) :
    let I := Ideal.span (Set.range g)
    let qbar : Ideal (MvPolynomial (Fin n) R ⧸ I) :=
      q.map (Ideal.Quotient.mk I)
    let x : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ I) :=
      ⟨qbar, Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩
    let f : Spec (.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))
    f.UnramifiedAt x := sorry

/-- Full row rank of the `n × m` residue-field Jacobian forces `n ≤ m`. -/
theorem variableCount_le_relationCount {R : Type u} [CommRing R] (n m : ℕ)
    (g : Fin m → MvPolynomial (Fin n) R)
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hIq : Ideal.span (Set.range g) ≤ q)
    (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n) :
    n ≤ m := sorry

/-- In the square full-rank case, the quotient-spectrum morphism is flat at `q / I`. -/
theorem flatAt_of_square {R : Type u} [CommRing R] (n : ℕ)
    (g : Fin n → MvPolynomial (Fin n) R)
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hIq : Ideal.span (Set.range g) ≤ q)
    (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n) :
    let I := Ideal.span (Set.range g)
    let qbar : Ideal (MvPolynomial (Fin n) R ⧸ I) :=
      q.map (Ideal.Quotient.mk I)
    let x : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ I) :=
      ⟨qbar, Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩
    let f : Spec (.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))
    f.flatAt x := sorry

/-- In the square full-rank case, the quotient-spectrum morphism is étale at `q / I`. -/
theorem etaleAt_of_square {R : Type u} [CommRing R] (n : ℕ)
    (g : Fin n → MvPolynomial (Fin n) R)
    (q : Ideal (MvPolynomial (Fin n) R)) [q.IsPrime]
    (hIq : Ideal.span (Set.range g) ≤ q)
    (h_rank : (MvPolynomial.jacobiMatrixAt g q).rank = n) :
    let I := Ideal.span (Set.range g)
    let qbar : Ideal (MvPolynomial (Fin n) R ⧸ I) :=
      q.map (Ideal.Quotient.mk I)
    let x : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ I) :=
      ⟨qbar, Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩
    let f : Spec (.of (MvPolynomial (Fin n) R ⧸ I)) ⟶ Spec (.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (Fin n) R ⧸ I)))
    f.EtaleAt x := sorry

end AlgebraicGeometry.JacobianCriterion
