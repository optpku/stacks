/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation.BaseChange
import StacksCheckRecall

/-!
# Scalar extension of two-term Ext annihilation

This file is the source-facing recall for Lemma 15.85.7.

@stack 0G9H
-/

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 15.85.7: the equivalent two-term Ext-annihilation conditions persist after scalar
extension and truncation in degrees `≥ -1`. -/
@[stacks 0G9H "Lemma 15.85.7"]
#check fun {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hcond : admits_two_term_free_representative_with_ideal_factorization K I) =>
  (TwoTermExtAnnihilation.extension_tfae σ K I hcond :
    let K' := (t.truncGE (-1)).obj ((ModuleCat.derivedExtensionOfScalars σ).obj K)
    let I' := Ideal.map σ I
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K' I',
      admits_two_term_free_representative_with_ideal_factorization K' I',
      all_two_term_projective_representatives_have_ideal_factorization K' I'] ∧
        admits_two_term_free_representative_with_ideal_factorization K' I')
