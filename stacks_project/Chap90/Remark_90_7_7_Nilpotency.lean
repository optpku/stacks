module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Lemma_90_7_4_Filtration

/-!
# Nilpotency index of an Artinian local algebra

A local Artinian ring has some vanishing maximal-adic power. The least Lean truncation
index `n` with `maximalIdeal ^ (n + 1) = ⊥` identifies `A ⧸ m_A^{n+1}` with `A`, and
the zero ideal filtration of an Artinian complete local algebra induces the
maximal-adic topology.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Existence of a truncation index at which a positive maximal-adic power vanishes. -/
noncomputable def exists_nilpotencyIndex (A : ArtinianLocalAlgCat Λ k) :
    ∃ n, maximalIdeal A.carrier ^ (n + 1) = ⊥ :=
  Exists.elim
    ((isArtinianRing_iff_isNilpotent_maximalIdeal A.carrier).mp inferInstance)
    (fun k hk ↦
      ⟨k, le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans (le_of_eq hk))⟩)

/-- Least `n` such that `maximalIdeal A ^ (n + 1) = ⊥`, matching truncation indexing. -/
noncomputable def nilpotencyIndex (A : ArtinianLocalAlgCat Λ k) : ℕ :=
  @Nat.find (fun n ↦ maximalIdeal A.carrier ^ (n + 1) = ⊥)
    (fun _ ↦ Classical.propDecidable _) (exists_nilpotencyIndex A)

/-- The maximal-adic power at `nilpotencyIndex A` is the zero ideal. -/
def nilpotencyIndex_pow_eq_bot (A : ArtinianLocalAlgCat Λ k) :
    maximalIdeal A.carrier ^ (nilpotencyIndex A + 1) = ⊥ :=
  @Nat.find_spec (fun n ↦ maximalIdeal A.carrier ^ (n + 1) = ⊥)
    (fun _ ↦ Classical.propDecidable _) (exists_nilpotencyIndex A)

/-- Canonical quotient map `A ⟶ A ⧸ maximalIdeal A ^ (n + 1)` in `C_Λ`. -/
noncomputable def toTruncation (A : ArtinianLocalAlgCat Λ k) (n : ℕ) :
    A ⟶ (toComplete A).truncation n where
  hom := Ideal.Quotient.mkₐ Λ (maximalIdeal A.carrier ^ (n + 1))
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `toTruncation` is the canonical quotient map. -/
theorem toTruncation_hom (A : ArtinianLocalAlgCat Λ k) (n : ℕ) :
    (toTruncation A n).hom =
      Ideal.Quotient.mkₐ Λ (maximalIdeal A.carrier ^ (n + 1)) := sorry

/-- Algebra isomorphism `A ⧸ maximalIdeal A ^ (nilpotencyIndex A + 1) ≃ₐ[Λ] A`. -/
noncomputable def truncationNilpotencyAlgEquiv (A : ArtinianLocalAlgCat Λ k) :
    ((toComplete A).truncation (nilpotencyIndex A)).carrier ≃ₐ[Λ] A.carrier :=
  (Ideal.quotientEquivAlgOfEq Λ (nilpotencyIndex_pow_eq_bot A)).trans
    (AlgEquiv.quotientBot Λ A.carrier)

/-- Identification `(toComplete A).truncation (nilpotencyIndex A) ≅ A` in `C_Λ`. -/
noncomputable def truncationNilpotencyIso (A : ArtinianLocalAlgCat Λ k) :
    (toComplete A).truncation (nilpotencyIndex A) ≅ A where
  hom :=
    { hom := (truncationNilpotencyAlgEquiv A).toAlgHom
      isLocalHom := sorry
      residue_compat := sorry }
  inv :=
    { hom := (truncationNilpotencyAlgEquiv A).symm.toAlgHom
      isLocalHom := sorry
      residue_compat := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of `truncationNilpotencyIso` is the algebra isomorphism. -/
theorem truncationNilpotencyIso_hom (A : ArtinianLocalAlgCat Λ k) :
    (truncationNilpotencyIso A).hom.hom = (truncationNilpotencyAlgEquiv A).toAlgHom := sorry

end ArtinianLocalAlgCat

namespace CompleteLocalAlgCat.AdicIdealFiltration

/-- The zero-ideal filtration of an Artinian complete local algebra. -/
noncomputable def zero (R : CompleteLocalAlgCat Λ k) [IsArtinianRing R.carrier] :
    AdicIdealFiltration R where
  ideal := fun _ ↦ ⊥
  antitone := fun _ _ _ ↦ le_rfl
  le_maximal := fun _ ↦ bot_le
  exists_le_pow := fun _ ↦ ⟨0, bot_le⟩
  exists_pow_le := fun _ ↦
    Exists.elim
      ((isArtinianRing_iff_isNilpotent_maximalIdeal R.carrier).mp inferInstance)
      (fun k hk ↦
        ⟨k, (Ideal.pow_le_pow_right (Nat.le_succ k)).trans (le_of_eq hk)⟩)

/-- Every stage of the zero filtration is the zero ideal. -/
theorem zero_ideal (R : CompleteLocalAlgCat Λ k) [IsArtinianRing R.carrier] (n : ℕ) :
    (zero R).ideal n = ⊥ := sorry

end CompleteLocalAlgCat.AdicIdealFiltration
