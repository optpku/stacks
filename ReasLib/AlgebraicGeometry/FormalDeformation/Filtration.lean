/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal

/-!
# Ideal filtrations of complete local algebras

This file records explicit filtrations cofinal with the positive powers of the
maximal ideal and the associated Artinian-local quotients.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- A decreasing ideal filtration cofinal with the positive maximal-adic powers. -/
structure AdicIdealFiltration (R : CompleteLocalAlgCat Λ k) where
  ideal : ℕ → Ideal R.carrier
  antitone : Antitone ideal
  le_maximal : ∀ n, ideal n ≤ maximalIdeal R
  exists_le_pow : ∀ n, ∃ m, ideal m ≤ maximalIdeal R ^ (n + 1)
  exists_pow_le : ∀ n, ∃ m, maximalIdeal R ^ (m + 1) ≤ ideal n

namespace AdicIdealFiltration

variable {R : CompleteLocalAlgCat Λ k}

/-- Construct a filtration from its antitone and cofinality data. -/
def of (ideal : ℕ → Ideal R.carrier) (antitone : Antitone ideal)
    (le_maximal : ∀ n, ideal n ≤ maximalIdeal R)
    (exists_le_pow : ∀ n, ∃ m, ideal m ≤ maximalIdeal R ^ (n + 1))
    (exists_pow_le : ∀ n, ∃ m, maximalIdeal R ^ (m + 1) ≤ ideal n) :
    AdicIdealFiltration R :=
  ⟨ideal, antitone, le_maximal, exists_le_pow, exists_pow_le⟩

/-- The defining antitone and cofinality conditions of a filtration. -/
theorem spec (I : AdicIdealFiltration R) :
    Antitone I.ideal ∧ (∀ n, I.ideal n ≤ maximalIdeal R) ∧
      (∀ n, ∃ m, I.ideal m ≤ maximalIdeal R ^ (n + 1)) ∧
      (∀ n, ∃ m, maximalIdeal R ^ (m + 1) ≤ I.ideal n) := sorry

/-- Characterization of ideal families that define admissible filtrations. -/
theorem spec_iff (J : ℕ → Ideal R.carrier) :
    (∃ I : AdicIdealFiltration R, I.ideal = J) ↔
      Antitone J ∧ (∀ n, J n ≤ maximalIdeal R) ∧
        (∀ n, ∃ m, J m ≤ maximalIdeal R ^ (n + 1)) ∧
        (∀ n, ∃ m, maximalIdeal R ^ (m + 1) ≤ J n) := sorry

/-- The positive maximal-adic powers form an admissible filtration. -/
def maximalAdic (R : CompleteLocalAlgCat Λ k) : AdicIdealFiltration R where
  ideal n := maximalIdeal R ^ (n + 1)
  antitone := fun _ _ h ↦ Ideal.pow_le_pow_right (Nat.succ_le_succ h)
  le_maximal := fun n ↦ Ideal.pow_le_self (Nat.succ_ne_zero n)
  exists_le_pow := fun n ↦ ⟨n, le_rfl⟩
  exists_pow_le := fun n ↦ ⟨n, le_rfl⟩

/-- The ideals in the standard maximal-adic filtration. -/
theorem maximalAdic_ideal (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (maximalAdic R).ideal n = maximalIdeal R ^ (n + 1) := sorry

variable (I : AdicIdealFiltration R)

/-- The inherited `Λ`-algebra structure on a filtration quotient. -/
noncomputable def quotientAlgebra (n : ℕ) : Algebra Λ (R.carrier ⧸ I.ideal n) :=
  @Ideal.Quotient.algebra Λ R.carrier inferInstance inferInstance R.algebra
    (I.ideal n) inferInstance

/-- The quotient by a filtration stage is nontrivial. -/
theorem quotient_nontrivial (n : ℕ) : Nontrivial (R.carrier ⧸ I.ideal n) := by
  -- Local instance justification (defeq pin): identify the maximal ideal using the stored local-ring proof.
  letI := R.isLocalRing
  exact Ideal.Quotient.nontrivial_iff.mpr
    (mt (fun h ↦ eq_top_iff.2 (h.symm.trans_le (I.le_maximal n)))
      (Ideal.IsMaximal.ne_top inferInstance))

/-- The quotient by a filtration stage is a local ring. -/
theorem quotient_isLocalRing (n : ℕ) : IsLocalRing (R.carrier ⧸ I.ideal n) := by
  -- Local instance justification (proof-local temporary data): apply the surjective local-ring theorem to the stored source local ring.
  letI := R.isLocalRing
  -- Local instance justification (proof-local temporary data): the surjective local-ring theorem requires nontriviality of this quotient.
  letI := I.quotient_nontrivial n
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.ideal n))
    Ideal.Quotient.mk_surjective

/-- The quotient by a filtration stage is Artinian. -/
theorem quotient_isArtinianRing (n : ℕ) : IsArtinianRing (R.carrier ⧸ I.ideal n) := sorry

/-- The residue-field identification of a filtration quotient with `k`. -/
noncomputable def truncationResidueFieldIso (n : ℕ) :
    @AlgEquiv Λ (@ResidueField (R.carrier ⧸ I.ideal n) inferInstance
      (I.quotient_isLocalRing n)) k _ _ _
      (@ResidueField.algebra (R.carrier ⧸ I.ideal n) inferInstance
        (I.quotient_isLocalRing n) Λ inferInstance (I.quotientAlgebra n)) inferInstance := by
  -- Local instance justification (defeq pin): the quotient residue-field equivalence uses the algebra stored in the source object.
  letI := R.algebra
  -- Local instance justification (defeq pin): the quotient residue-field equivalence uses the maximal ideal from the stored local-ring proof.
  letI := R.isLocalRing
  -- Local instance justification (defeq pin): the residue-field algebra must reduce to the specified filtration quotient algebra.
  letI := I.quotientAlgebra n
  -- Local instance justification (defeq pin): the quotient residue field must use the stored quotient local-ring proof.
  letI := I.quotient_isLocalRing n
  exact (Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (I.ideal n)) Ideal.Quotient.mk_surjective).symm).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ (I.le_maximal n)).trans R.residueFieldIso)

/-- The Artinian-local quotient associated to a filtration stage. -/
noncomputable def truncation (n : ℕ) : ArtinianLocalAlgCat Λ k :=
  ⟨CommRingCat.of (R.carrier ⧸ I.ideal n), I.quotientAlgebra n,
    I.quotient_isLocalRing n, I.quotient_isArtinianRing n,
    I.truncationResidueFieldIso n⟩

/-- The carrier of a filtration truncation is its ideal quotient. -/
theorem truncation_carrier (n : ℕ) :
    (I.truncation n).carrier = (R.carrier ⧸ I.ideal n) := sorry

/-- The local, Artinian, and residue-field data of a filtration truncation. -/
theorem truncation_spec (n : ℕ) :
    IsArtinianRing (I.truncation n).carrier ∧ IsLocalRing (I.truncation n).carrier ∧
      (I.truncation n).residueFieldIso = I.truncationResidueFieldIso n := sorry

/-- The factor map between successive filtration quotients is local. -/
theorem truncationMap_isLocalHom (n : ℕ) :
    IsLocalHom (@Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
      (I.ideal (n + 1)) (I.ideal n) inferInstance inferInstance
      (I.antitone n.le_succ)) := sorry

/-- The factor map between successive filtration quotients respects residue identifications. -/
theorem truncationMap_residue_compat (n : ℕ) :
    ArtinianLocalAlgCat.residueCompat
      (A := I.truncation (n + 1)) (B := I.truncation n)
      (@Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
        (I.ideal (n + 1)) (I.ideal n) inferInstance inferInstance
        (I.antitone n.le_succ)) (I.truncationMap_isLocalHom n) =
      ArtinianLocalAlgCat.residueIsoHom (I.truncation (n + 1)) := sorry

/-- The projection between successive filtration quotients. -/
noncomputable def truncationMap (n : ℕ) :
    ArtinianLocalAlgCat.Hom (I.truncation (n + 1)) (I.truncation n) :=
  ArtinianLocalAlgCat.Hom.of (A := I.truncation (n + 1)) (B := I.truncation n)
    (@Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
      (I.ideal (n + 1)) (I.ideal n) inferInstance inferInstance
      (I.antitone n.le_succ)) (I.truncationMap_isLocalHom n)
    (I.truncationMap_residue_compat n)

/-- The underlying algebra map of a filtration projection. -/
theorem truncationMap_hom (n : ℕ) :
    (I.truncationMap n).hom =
      @Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
        (I.ideal (n + 1)) (I.ideal n) inferInstance inferInstance
        (I.antitone n.le_succ) := sorry

/-- Decidability of containment in a maximal-adic power. -/
@[reducible] noncomputable def lePowDecidable (n : ℕ) :
    DecidablePred (fun m ↦ I.ideal m ≤ maximalIdeal R ^ (n + 1)) :=
  fun _ ↦ Classical.propDecidable _

/-- The least stage contained in a given positive maximal-adic power. -/
noncomputable def stageIndex (n : ℕ) : ℕ :=
  @Nat.find (fun m ↦ I.ideal m ≤ maximalIdeal R ^ (n + 1))
    (I.lePowDecidable n) (I.exists_le_pow n)

/-- The selected stage is contained in the corresponding maximal-adic power. -/
theorem stageIndex_le (n : ℕ) :
    I.ideal (I.stageIndex n) ≤ maximalIdeal R ^ (n + 1) :=
  @Nat.find_spec (fun m ↦ I.ideal m ≤ maximalIdeal R ^ (n + 1))
    (I.lePowDecidable n) (I.exists_le_pow n)

/-- The selected stages are monotone. -/
theorem stageIndex_mono (n : ℕ) : I.stageIndex n ≤ I.stageIndex (n + 1) :=
  @Nat.find_min' (fun m ↦ I.ideal m ≤ maximalIdeal R ^ (n + 1))
    (I.lePowDecidable n) (I.exists_le_pow n) (I.stageIndex (n + 1))
    (le_trans
      (@Nat.find_spec (fun m ↦ I.ideal m ≤ maximalIdeal R ^ (n + 1 + 1))
        (I.lePowDecidable (n + 1)) (I.exists_le_pow (n + 1)))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))

/-- The factor map from a selected filtration stage to a maximal-adic stage is local. -/
theorem truncationComparison_isLocalHom (n : ℕ) :
    IsLocalHom (@Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
      (I.ideal (I.stageIndex n)) (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1))
      inferInstance inferInstance (I.stageIndex_le n)) := sorry

/-- The comparison to a maximal-adic quotient respects residue identifications. -/
theorem truncationComparison_residue_compat (n : ℕ) :
    ArtinianLocalAlgCat.residueCompat
      (A := I.truncation (I.stageIndex n)) (B := R.truncation n)
      (@Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
        (I.ideal (I.stageIndex n)) (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1))
        inferInstance inferInstance (I.stageIndex_le n))
      (I.truncationComparison_isLocalHom n) =
      ArtinianLocalAlgCat.residueIsoHom (I.truncation (I.stageIndex n)) := sorry

/-- The quotient comparison from a selected filtration stage to a maximal-adic stage. -/
noncomputable def truncationComparison (n : ℕ) :
    ArtinianLocalAlgCat.Hom (I.truncation (I.stageIndex n)) (R.truncation n) :=
  ArtinianLocalAlgCat.Hom.of (A := I.truncation (I.stageIndex n)) (B := R.truncation n)
    (@Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
      (I.ideal (I.stageIndex n)) (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1))
      inferInstance inferInstance (I.stageIndex_le n))
    (I.truncationComparison_isLocalHom n) (I.truncationComparison_residue_compat n)

/-- The underlying algebra map of a quotient comparison. -/
theorem truncationComparison_hom (n : ℕ) :
    (I.truncationComparison n).hom =
      @Ideal.Quotient.factorₐ Λ R.carrier inferInstance inferInstance R.algebra
        (I.ideal (I.stageIndex n)) (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1))
        inferInstance inferInstance (I.stageIndex_le n) := sorry

end AdicIdealFiltration

end CompleteLocalAlgCat
