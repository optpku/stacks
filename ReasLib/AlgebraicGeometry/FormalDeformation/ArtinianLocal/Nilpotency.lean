module

public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Inclusion
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal

/-!
# Nilpotency and truncations of Artinian local algebras
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Existence of a truncation index at which a positive maximal-adic power vanishes. -/
noncomputable def exists_nilpotencyIndex (A : ArtinianLocalAlgCat Λ k) :
    ∃ n, CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (n + 1) = ⊥ :=
  Exists.elim
    ((@isArtinianRing_iff_isNilpotent_maximalIdeal A.carrier A.carrier.commRing
      (@instIsNoetherianRingOfIsArtinianRing A.carrier A.carrier.commRing.toRing A.isArtinianRing)
      A.isLocalRing).mp A.isArtinianRing)
    (fun k hk ↦
      ⟨k, le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans (le_of_eq hk))⟩)

/-- Least `n` such that `maximalIdeal A ^ (n + 1) = ⊥`, matching truncation indexing. -/
noncomputable def nilpotencyIndex (A : ArtinianLocalAlgCat Λ k) : ℕ :=
  @Nat.find (fun n ↦ CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (n + 1) = ⊥)
    (fun _ ↦ Classical.propDecidable _) (exists_nilpotencyIndex A)

/-- The maximal-adic power at `nilpotencyIndex A` is the zero ideal. -/
def nilpotencyIndex_pow_eq_bot (A : ArtinianLocalAlgCat Λ k) :
    CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (nilpotencyIndex A + 1) = ⊥ :=
  @Nat.find_spec (fun n ↦ CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (n + 1) = ⊥)
    (fun _ ↦ Classical.propDecidable _) (exists_nilpotencyIndex A)

/-- The canonical quotient algebra map to a maximal-adic truncation is local. -/
theorem toTruncation_isLocalHom (A : ArtinianLocalAlgCat Λ k) (n : ℕ) :
    IsLocalHom (@Ideal.Quotient.mkₐ Λ A.carrier _ _ A.algebra
      (CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (n + 1)) inferInstance) := sorry

/-- The quotient map to a maximal-adic truncation preserves the residue identification. -/
theorem toTruncation_residue_compat (A : ArtinianLocalAlgCat Λ k) (n : ℕ) :
    residueCompat (A := A) (B := (toComplete A).truncation n)
      (@Ideal.Quotient.mkₐ Λ A.carrier _ _ A.algebra
      (CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (n + 1)) inferInstance)
      (toTruncation_isLocalHom A n) = residueIsoHom A := sorry

/-- The canonical quotient morphism to a maximal-adic truncation. -/
noncomputable def toTruncation (A : ArtinianLocalAlgCat Λ k) (n : ℕ) :
    A ⟶ (toComplete A).truncation n :=
  Hom.of (@Ideal.Quotient.mkₐ Λ A.carrier _ _ A.algebra
      (CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (n + 1)) inferInstance)
    (toTruncation_isLocalHom A n) (toTruncation_residue_compat A n)

/-- The underlying algebra map of `toTruncation` is the canonical quotient map. -/
theorem toTruncation_hom (A : ArtinianLocalAlgCat Λ k) (n : ℕ) :
    (toTruncation A n).hom =
      @Ideal.Quotient.mkₐ Λ A.carrier _ _ A.algebra
      (CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (n + 1)) inferInstance := sorry

/-- Algebra isomorphism `A ⧸ maximalIdeal A ^ (nilpotencyIndex A + 1) ≃ₐ[Λ] A`. -/
noncomputable def truncationNilpotencyAlgEquiv (A : ArtinianLocalAlgCat Λ k) :
    @AlgEquiv Λ ((toComplete A).truncation (nilpotencyIndex A)).carrier A.carrier _ _ _
      ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra := by
  let equiv (R : Type u) [CommRing R] [Algebra Λ R] (I : Ideal R) (h : I = ⊥) :
      (R ⧸ I) ≃ₐ[Λ] R :=
    (Ideal.quotientEquivAlgOfEq Λ h).trans (AlgEquiv.quotientBot Λ R)
  exact @equiv A.carrier A.carrier.commRing A.algebra
    (CompleteLocalAlgCat.maximalIdeal (toComplete A) ^ (nilpotencyIndex A + 1))
    (nilpotencyIndex_pow_eq_bot A)

/-- The nilpotency-stage quotient equivalence is local in the forward direction. -/
theorem truncationNilpotencyHom_isLocalHom (A : ArtinianLocalAlgCat Λ k) :
    IsLocalHom (@AlgEquiv.toAlgHom Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A)) := sorry

/-- The nilpotency-stage equivalence preserves the residue identification. -/
theorem truncationNilpotencyHom_residue_compat (A : ArtinianLocalAlgCat Λ k) :
    residueCompat (A := (toComplete A).truncation (nilpotencyIndex A)) (B := A)
      (@AlgEquiv.toAlgHom Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A))
      (truncationNilpotencyHom_isLocalHom A) =
        residueIsoHom ((toComplete A).truncation (nilpotencyIndex A)) := sorry

/-- The inverse nilpotency-stage quotient equivalence is local. -/
theorem truncationNilpotencyInv_isLocalHom (A : ArtinianLocalAlgCat Λ k) :
    IsLocalHom (@AlgEquiv.toAlgHom Λ _ _ _ _ _ A.algebra ((toComplete A).truncation (nilpotencyIndex A)).algebra
      (@AlgEquiv.symm Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A))) := sorry

/-- The inverse nilpotency-stage equivalence preserves the residue identification. -/
theorem truncationNilpotencyInv_residue_compat (A : ArtinianLocalAlgCat Λ k) :
    residueCompat (A := A) (B := (toComplete A).truncation (nilpotencyIndex A))
      (@AlgEquiv.toAlgHom Λ _ _ _ _ _ A.algebra ((toComplete A).truncation (nilpotencyIndex A)).algebra
      (@AlgEquiv.symm Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A)))
      (truncationNilpotencyInv_isLocalHom A) = residueIsoHom A := sorry

/-- The quotient equivalence followed by its inverse is the identity. -/
theorem truncationNilpotencyHom_inv_id (A : ArtinianLocalAlgCat Λ k) :
    Hom.of (@AlgEquiv.toAlgHom Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A))
        (truncationNilpotencyHom_isLocalHom A) (truncationNilpotencyHom_residue_compat A) ≫
      Hom.of (@AlgEquiv.toAlgHom Λ _ _ _ _ _ A.algebra ((toComplete A).truncation (nilpotencyIndex A)).algebra
      (@AlgEquiv.symm Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A)))
        (truncationNilpotencyInv_isLocalHom A) (truncationNilpotencyInv_residue_compat A) =
      𝟙 ((toComplete A).truncation (nilpotencyIndex A)) := sorry

/-- The inverse quotient equivalence followed by the equivalence is the identity. -/
theorem truncationNilpotencyInv_hom_id (A : ArtinianLocalAlgCat Λ k) :
    Hom.of (@AlgEquiv.toAlgHom Λ _ _ _ _ _ A.algebra ((toComplete A).truncation (nilpotencyIndex A)).algebra
      (@AlgEquiv.symm Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A)))
        (truncationNilpotencyInv_isLocalHom A) (truncationNilpotencyInv_residue_compat A) ≫
      Hom.of (@AlgEquiv.toAlgHom Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A))
        (truncationNilpotencyHom_isLocalHom A) (truncationNilpotencyHom_residue_compat A) =
      𝟙 A := sorry

/-- The nilpotency-stage truncation is canonically isomorphic to the Artinian algebra. -/
noncomputable def truncationNilpotencyIso (A : ArtinianLocalAlgCat Λ k) :
    (toComplete A).truncation (nilpotencyIndex A) ≅ A where
  hom := Hom.of (@AlgEquiv.toAlgHom Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A))
    (truncationNilpotencyHom_isLocalHom A) (truncationNilpotencyHom_residue_compat A)
  inv := Hom.of (@AlgEquiv.toAlgHom Λ _ _ _ _ _ A.algebra ((toComplete A).truncation (nilpotencyIndex A)).algebra
      (@AlgEquiv.symm Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A)))
    (truncationNilpotencyInv_isLocalHom A) (truncationNilpotencyInv_residue_compat A)
  hom_inv_id := truncationNilpotencyHom_inv_id A
  inv_hom_id := truncationNilpotencyInv_hom_id A

/-- The forward morphism of `truncationNilpotencyIso` is the algebra isomorphism. -/
theorem truncationNilpotencyIso_hom (A : ArtinianLocalAlgCat Λ k) :
    (truncationNilpotencyIso A).hom.hom = (@AlgEquiv.toAlgHom Λ _ _ _ _ _ ((toComplete A).truncation (nilpotencyIndex A)).algebra A.algebra (truncationNilpotencyAlgEquiv A)) := sorry

end ArtinianLocalAlgCat

