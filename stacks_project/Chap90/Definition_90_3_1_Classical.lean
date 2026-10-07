module

public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Classical standing hypotheses for `ArtinianLocalAlgCat`

The classical case of the base category is the standing assumption that `Λ` is a
Noetherian complete local ring and that the finite `Λ`-field `k` is its residue
field. Surjectivity of `algebraMap Λ k` encodes that identification.
-/

@[expose] public section

open IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The classical case: `Λ` is complete local and `k` is its residue field. -/
class IsClassical : Prop extends IsCompleteLocalRing Λ where
  /-- The structure map `Λ → k` is surjective, so `k` is the residue field of `Λ`. -/
  algebraMap_surjective : Function.Surjective (algebraMap Λ k)

variable {Λ k}

/-- The residue field of a complete local ring is a classical choice of `k`. -/
instance instIsClassicalResidueField [IsCompleteLocalRing Λ] :
    IsClassical Λ (ResidueField Λ) where
  algebraMap_surjective := residue_surjective

/-- Classical standing hypotheses are completeness of `Λ` together with surjectivity of
`algebraMap Λ k`. -/
theorem isClassical_iff :
    IsClassical Λ k ↔ IsCompleteLocalRing Λ ∧ Function.Surjective (algebraMap Λ k) := sorry

/-- In the classical case, the residue field of `Λ` is identified with `k`. -/
noncomputable def IsClassical.residueFieldIso [IsClassical Λ k] :
    ResidueField Λ ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (ker_eq_maximalIdeal (Algebra.ofId Λ k : Λ →+* k) algebraMap_surjective).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (algebraMap_surjective : Function.Surjective (Algebra.ofId Λ k)))

/-- The classical residue identification sends `residue Λ x` to `algebraMap Λ k x`. -/
theorem IsClassical.residueFieldIso_residue [IsClassical Λ k] (x : Λ) :
    IsClassical.residueFieldIso (residue Λ x) = algebraMap Λ k x := sorry

/-- An explicit residue-field identification witnesses the classical case. -/
theorem ofResidueFieldIso [IsCompleteLocalRing Λ] (e : ResidueField Λ ≃ₐ[Λ] k) :
    IsClassical Λ k := sorry

end ArtinianLocalAlgCat
