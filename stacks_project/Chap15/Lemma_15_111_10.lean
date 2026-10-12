/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.FieldTheory.Galois.IntegralClosure.ResidueField

/-!
# Lemma 15.111.10

@stack 0BRK
-/

@[expose] public section

open scoped Pointwise

universe u v w

/-
Lemma 15.111.10 (current Stacks numbering: Lemma 15.112.10, tag `0BRK`).
Let `A` be a normal domain with fraction field `K`, let `L / K` be a possibly
infinite Galois extension, and let `B = integralClosure A L`.

(1) `Gal(L/K)` acts transitively on the primes of `B` above a fixed prime of
    `A`.
(2) For `q` above `p`, the residue-field extension `κ(q) / κ(p)` is normal.
(3) The decomposition group of `q` surjects onto `Aut(κ(q) / κ(p))`.

The checks below use the profinite ReasLib owners.  In particular, clauses (2)
and (3) do not specialize the finite-group API from Lemma 15.111.9.
-/

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type w} [Field L] [Algebra A L] [Algebra K L]
variable [IsScalarTower A K L] [IsGalois K L]

@[stacks 0BRK "Lemma 15.111.10 (1)"]
#check fun (p : Ideal A) [p.IsPrime]
    (q q' : Ideal (integralClosure A L)) [q.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [q'.LiesOver p] ↦
  (integralClosure.exists_smul_eq_of_under_eq (K := K) q q'
    ((q.over_def p).symm.trans (q'.over_def p)) :
    ∃ σ : Gal(L/K), σ • q = q')

@[stacks 0BRK "Lemma 15.111.10 (2)"]
#check fun (p : Ideal A) [p.IsPrime]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p] ↦
  (integralClosure.ResidueField.normal (K := K) p q :
    letI : Algebra p.ResidueField q.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p q
    Normal p.ResidueField q.ResidueField)

@[stacks 0BRK "Lemma 15.111.10 (3)"]
#check fun (p : Ideal A) [p.IsPrime]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver p] ↦
  (integralClosure.ResidueField.stabilizerHom_surjective (K := K) p q :
    Function.Surjective
      (Ideal.ResidueField.Invariant.stabilizerHom (G := Gal(L/K)) p q))

end
