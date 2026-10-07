module

public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# Sequential ideal filtrations inducing the maximal-adic topology

A decreasing sequence of ideals of a complete local algebra `R` that is cofinal
with the powers of `maximalIdeal R` in both directions, and contained in the
maximal ideal, so that each quotient `R ⧸ I n` lies in `C_Λ`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- A decreasing ideal filtration of a complete local algebra that induces the
maximal-adic topology and remains inside the maximal ideal. -/
structure AdicIdealFiltration (R : CompleteLocalAlgCat Λ k) where
  /-- The underlying decreasing family of ideals. -/
  ideal : ℕ → Ideal R.carrier
  /-- The family is antitone. -/
  antitone : Antitone ideal
  /-- Each ideal is contained in the maximal ideal, so the quotient is local with
  residue field `k`. -/
  le_maximal : ∀ n, ideal n ≤ maximalIdeal R.carrier
  /-- Every maximal-adic power contains some stage of the filtration. -/
  exists_le_pow : ∀ n, ∃ m, ideal m ≤ maximalIdeal R.carrier ^ (n + 1)
  /-- Every stage of the filtration contains some maximal-adic power. -/
  exists_pow_le : ∀ n, ∃ m, maximalIdeal R.carrier ^ (m + 1) ≤ ideal n

namespace AdicIdealFiltration

variable {R : CompleteLocalAlgCat Λ k}

/-- Package an antitone, maximal-adic equivalent ideal family as a filtration. -/
def of (ideal : ℕ → Ideal R.carrier) (antitone : Antitone ideal)
    (le_maximal : ∀ n, ideal n ≤ maximalIdeal R.carrier)
    (exists_le_pow : ∀ n, ∃ m, ideal m ≤ maximalIdeal R.carrier ^ (n + 1))
    (exists_pow_le : ∀ n, ∃ m, maximalIdeal R.carrier ^ (m + 1) ≤ ideal n) :
    AdicIdealFiltration R where
  ideal := ideal
  antitone := antitone
  le_maximal := le_maximal
  exists_le_pow := exists_le_pow
  exists_pow_le := exists_pow_le

/-- A filtration is antitone, contained in the maximal ideal, and cofinal with the
maximal-adic powers in both directions. -/
theorem spec (I : AdicIdealFiltration R) :
    Antitone I.ideal ∧ (∀ n, I.ideal n ≤ maximalIdeal R.carrier) ∧
      (∀ n, ∃ m, I.ideal m ≤ maximalIdeal R.carrier ^ (n + 1)) ∧
      (∀ n, ∃ m, maximalIdeal R.carrier ^ (m + 1) ≤ I.ideal n) := sorry

/-- An ideal family arises from an `AdicIdealFiltration` iff it is antitone, contained
in the maximal ideal, and cofinal with the maximal-adic powers in both directions. -/
theorem spec_iff (J : ℕ → Ideal R.carrier) :
    (∃ I : AdicIdealFiltration R, I.ideal = J) ↔
      Antitone J ∧ (∀ n, J n ≤ maximalIdeal R.carrier) ∧
        (∀ n, ∃ m, J m ≤ maximalIdeal R.carrier ^ (n + 1)) ∧
        (∀ n, ∃ m, maximalIdeal R.carrier ^ (m + 1) ≤ J n) := sorry

/-- The standard maximal-adic filtration `n ↦ maximalIdeal R ^ (n + 1)`. -/
def maximalAdic (R : CompleteLocalAlgCat Λ k) : AdicIdealFiltration R where
  ideal n := maximalIdeal R.carrier ^ (n + 1)
  antitone := fun _ _ h ↦ Ideal.pow_le_pow_right (Nat.succ_le_succ h)
  le_maximal := fun n ↦ Ideal.pow_le_self (Nat.succ_ne_zero n)
  exists_le_pow := fun n ↦ ⟨n, le_rfl⟩
  exists_pow_le := fun n ↦ ⟨n, le_rfl⟩

/-- The underlying ideals of `maximalAdic` are the positive maximal-adic powers. -/
theorem maximalAdic_ideal (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    (maximalAdic R).ideal n = maximalIdeal R.carrier ^ (n + 1) := sorry

variable (I : AdicIdealFiltration R)

/-- Quotients by filtration stages are nontrivial, since each stage is contained in
the maximal ideal. -/
instance instNontrivial_quotient (n : ℕ) : Nontrivial (R.carrier ⧸ I.ideal n) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (mt (fun h ↦ eq_top_iff.2 (h.symm.trans_le (I.le_maximal n)))
      (Ideal.IsMaximal.ne_top inferInstance))

/-- Quotients by filtration stages are local. -/
instance instIsLocalRing_quotient (n : ℕ) : IsLocalRing (R.carrier ⧸ I.ideal n) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (I.ideal n)) Ideal.Quotient.mk_surjective

/-- Quotients by filtration stages are Artinian, since some maximal-adic power is
contained in the stage. -/
instance instIsArtinianRing_quotient (n : ℕ) : IsArtinianRing (R.carrier ⧸ I.ideal n) :=
  sorry

/-- Canonical residue identification of `R ⧸ I n` with `k`. -/
noncomputable def truncationResidueFieldIso (n : ℕ) :
    ResidueField (R.carrier ⧸ I.ideal n) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (I.ideal n)) Ideal.Quotient.mk_surjective).symm).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ (I.le_maximal n)).trans R.residueFieldIso)

/-- The truncation `R ⧸ I n`, viewed as an object of `C_Λ`. -/
noncomputable def truncation (n : ℕ) : ArtinianLocalAlgCat Λ k :=
  ArtinianLocalAlgCat.of (R.carrier ⧸ I.ideal n) (I.truncationResidueFieldIso n)

/-- The carrier of an `I`-truncation is the corresponding ideal quotient. -/
theorem truncation_carrier (n : ℕ) :
    (I.truncation n).carrier = (R.carrier ⧸ I.ideal n) := sorry

/-- An `I`-truncation is Artinian local and residue-identified with `k`. -/
theorem truncation_spec (n : ℕ) :
    IsArtinianRing (I.truncation n).carrier ∧ IsLocalRing (I.truncation n).carrier ∧
      (I.truncation n).residueFieldIso = I.truncationResidueFieldIso n := sorry

/-- Canonical projection `R ⧸ I (n + 1) ⟶ R ⧸ I n`. -/
noncomputable def truncationMap (n : ℕ) :
    I.truncation (n + 1) ⟶ I.truncation n where
  hom := Ideal.Quotient.factorₐ Λ (I.antitone n.le_succ)
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of a filtration truncation projection is the canonical
factor map. -/
theorem truncationMap_hom (n : ℕ) :
    (I.truncationMap n).hom = Ideal.Quotient.factorₐ Λ (I.antitone n.le_succ) := sorry

/-- Classical decidability of containment in a maximal-adic power, used to pick the
least cofinal stage. -/
noncomputable def lePowDecidable (n : ℕ) :
    DecidablePred (fun m ↦ I.ideal m ≤ maximalIdeal R.carrier ^ (n + 1)) :=
  fun _ ↦ Classical.propDecidable _

/-- Least index `m` such that `I.ideal m ≤ maximalIdeal R ^ (n + 1)`. -/
noncomputable def stageIndex (n : ℕ) : ℕ :=
  @Nat.find (fun m ↦ I.ideal m ≤ maximalIdeal R.carrier ^ (n + 1))
    (I.lePowDecidable n) (I.exists_le_pow n)

/-- The stage `stageIndex n` is contained in the `n`th maximal-adic power. -/
def stageIndex_le (n : ℕ) :
    I.ideal (I.stageIndex n) ≤ maximalIdeal R.carrier ^ (n + 1) :=
  @Nat.find_spec (fun m ↦ I.ideal m ≤ maximalIdeal R.carrier ^ (n + 1))
    (I.lePowDecidable n) (I.exists_le_pow n)

/-- The least cofinal indices are monotone in the truncation degree. -/
def stageIndex_mono (n : ℕ) : I.stageIndex n ≤ I.stageIndex (n + 1) :=
  @Nat.find_min' (fun m ↦ I.ideal m ≤ maximalIdeal R.carrier ^ (n + 1))
    (I.lePowDecidable n) (I.exists_le_pow n) (I.stageIndex (n + 1))
    (le_trans
      (@Nat.find_spec (fun m ↦ I.ideal m ≤ maximalIdeal R.carrier ^ (n + 1 + 1))
        (I.lePowDecidable (n + 1)) (I.exists_le_pow (n + 1)))
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))))

/-- Canonical comparison `R ⧸ I_{m(n)} ⟶ R ⧸ maximalIdeal R ^ (n + 1)`. -/
noncomputable def truncationComparison (n : ℕ) :
    I.truncation (I.stageIndex n) ⟶ R.truncation n where
  hom := Ideal.Quotient.factorₐ Λ (I.stageIndex_le n)
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of a comparison map is the canonical factor map. -/
theorem truncationComparison_hom (n : ℕ) :
    (I.truncationComparison n).hom = Ideal.Quotient.factorₐ Λ (I.stageIndex_le n) := sorry

end AdicIdealFiltration

end CompleteLocalAlgCat
