/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.MvPolynomial.IrreducibleSpecialization

@[expose] public section

universe u v w x

/- Lemma 37.27.4: an absolutely irreducible multivariate polynomial over a domain remains
irreducible after every field-valued specialization from a suitable nonzero principal
localization. -/
@[stacks 0557] #check
  (MvPolynomial.exists_nonzero_away_irreducible_map :
    ∀ {A : Type u} [CommRing A] [IsDomain A]
      {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
      {Kbar : Type w} [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar]
      {n : ℕ} (P : MvPolynomial (Fin n) A),
      Irreducible (MvPolynomial.map ((algebraMap K Kbar).comp (algebraMap A K)) P) →
        ∃ f : A, f ≠ 0 ∧ ∀ {κ : Type x} [Field κ]
          (φ : Localization.Away f →+* κ),
          Irreducible (MvPolynomial.map (φ.comp (algebraMap A (Localization.Away f))) P))
