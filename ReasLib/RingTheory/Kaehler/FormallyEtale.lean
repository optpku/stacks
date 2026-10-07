module

public import Mathlib.RingTheory.Etale.Kaehler
public import ReasLib.RingTheory.Algebra.TensorProduct.FormallyEtale
public import ReasLib.RingTheory.RingHom.FormallyEtale.QuotientPow
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Diagonal quotient maps under formally etale base change

This leaf owns the quotient-thickening comparison attached to the diagonal
ideal after formally etale base change.  The tensor-product comparison and
the diagonal ideal remain canonical owner constructions; only their induced
map on an arbitrary quotient power is recorded here.
@stack 0H93
-/

open scoped TensorProduct

universe u v w

namespace KaehlerDifferential

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']

/-- Lemma 10.150.7 (1), tag `0H93`: in the generalized owner form, formal
etaleness of `S → S'` makes the canonical tensor-product comparison bijective
on the quotient by the `n`th power of the diagonal ideal for every `n : ℕ`.
The source's `k + 1` form is a specialization at `n = k + 1`. -/
@[stacks 0H93 "formally etale diagonal quotient powers"]
theorem diagonalQuotientMap_pow_bijective
    [Algebra.FormallyEtale S S'] (n : ℕ) :
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
        S' ⊗[R] S →+* S' ⊗[R] S')
    let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
    let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
    Function.Bijective
      ((Ideal.quotientMap (Jdiag ^ n) tensorComparison
          (Jdiag.le_comap_pow tensorComparison n)) :
        (S' ⊗[R] S) ⧸ (Icomap ^ n) →+* (S' ⊗[R] S') ⧸ (Jdiag ^ n)) := sorry

end KaehlerDifferential
