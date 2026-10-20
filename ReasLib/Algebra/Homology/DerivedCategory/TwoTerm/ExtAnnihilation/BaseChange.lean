module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar extension of two-term Ext-annihilation conditions

@stack 0G9H
-/

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory.TwoTermExtAnnihilation

/-- Lemma 15.85.7, commutative-ring specialization: the equivalent Ext-annihilation conditions
and their free-representative witness persist after scalar extension and truncation in degrees
`≥ -1`. -/
@[stacks 0G9H]
theorem extension_tfae
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S)
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hcond : admits_two_term_free_representative_with_ideal_factorization K I) :
    let K' := (t.truncGE (-1)).obj ((ModuleCat.derivedExtensionOfScalars σ).obj K)
    let I' := Ideal.map σ I
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K' I',
      admits_two_term_free_representative_with_ideal_factorization K' I',
      all_two_term_projective_representatives_have_ideal_factorization K' I'
    ] ∧ admits_two_term_free_representative_with_ideal_factorization K' I' := sorry
/- Proof strategy: unpack `hcond` to a free two-term representative, extend it termwise along
`σ`, and apply `IsTwoTermRepresentative.extension_truncGE`.  Map each factorization through the
extended differential and use `Ideal.map` to handle generators of `I'`; the resulting witness and
`two_term_ext1_annihilated_tfae` give the displayed conjunction. -/

end CategoryTheory.TwoTermExtAnnihilation
