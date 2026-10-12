/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace FieldExtension

/-- The canonical injection from the automorphism group `Gal(E/F)` into the set of
`F`-embeddings `Field.Emb F E`, given by composing an automorphism with the canonical
embedding into `AlgebraicClosure E`. -/
noncomputable def galToEmb
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] :
    Gal(E/F) → Field.Emb F E :=
  fun σ ↦ (IsScalarTower.toAlgHom F E (AlgebraicClosure E)).comp σ.toAlgHom

/-- The canonical map `galToEmb F E` from `Gal(E/F)` to `Field.Emb F E` is injective. -/
theorem galToEmb_injective
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] :
    Function.Injective (galToEmb F E) := by
  intro σ τ hστ
  ext x
  exact (IsScalarTower.toAlgHom F E (AlgebraicClosure E)).injective <| DFunLike.congr_fun hστ x

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

/-- Lemma 9.15.9 (Tag 09HS) (1): for a finite extension `E/F`, the number of
`F`-automorphisms of `E` is at most its finite separable degree. -/
theorem natCardGalLeFinSepDegree :
    Nat.card Gal(E/F) ≤ Field.finSepDegree F E := by
  simpa [Field.finSepDegree, galToEmb] using
    Nat.card_le_card_of_injective (galToEmb F E) (galToEmb_injective F E)

/-- Lemma 9.15.9 (2): for a finite extension `E/F`, equality between the number of
`F`-automorphisms and its finite separable degree is equivalent to normality. -/
theorem natCardGalEqFinSepDegreeIffNormal :
    Nat.card Gal(E/F) = Field.finSepDegree F E ↔ Normal F E := by
  constructor
  · intro h
    have hcard : Nat.card (Field.Emb F E) ≤ Nat.card Gal(E/F) := by
      exact le_of_eq <| calc
        Nat.card (Field.Emb F E) = Field.finSepDegree F E := rfl
        _ = Nat.card Gal(E/F) := h.symm
    have hbij : Function.Bijective (galToEmb F E) :=
      (galToEmb_injective F E).bijective_of_nat_card_le hcard
    let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E (AlgebraicClosure E)
    let e : E ≃ₐ[F] τ.fieldRange := AlgEquiv.ofInjectiveField τ
    have hfieldRange : ∀ ψ : τ.fieldRange →ₐ[F] AlgebraicClosure E, ψ.fieldRange = τ.fieldRange := by
      intro ψ
      rcases hbij.2 (ψ.comp e.toAlgHom) with ⟨σ, hσ⟩
      have hσtop : σ.toAlgHom.fieldRange = ⊤ := AlgEquiv.fieldRange_eq_top σ
      have hetop : e.toAlgHom.fieldRange = ⊤ := AlgEquiv.fieldRange_eq_top e
      have hcomp : (ψ.comp e.toAlgHom).fieldRange = τ.fieldRange := by
        calc
          (ψ.comp e.toAlgHom).fieldRange = ((galToEmb F E) σ).fieldRange := by
            simpa [galToEmb] using congrArg AlgHom.fieldRange hσ.symm
          _ = τ.fieldRange := by
            change (τ.comp σ.toAlgHom).fieldRange = τ.fieldRange
            rw [← AlgHom.map_fieldRange σ.toAlgHom τ, hσtop, ← AlgHom.fieldRange_eq_map τ]
      calc
        ψ.fieldRange = (ψ.comp e.toAlgHom).fieldRange := by
          rw [← AlgHom.map_fieldRange e.toAlgHom ψ, hetop, ← AlgHom.fieldRange_eq_map ψ]
        _ = τ.fieldRange := hcomp
    -- Local instance justification (proof-local temporary data): transfer the field-range normality criterion.
    letI : Normal F τ.fieldRange := (IntermediateField.normal_iff_forall_fieldRange_eq).2 hfieldRange
    exact Normal.of_algEquiv e.symm
  · intro h
    -- Local instance justification (proof-local temporary data): use the supplied normality hypothesis for the automorphism equivalence.
    letI : Normal F E := h
    simpa [Field.finSepDegree] using
      (Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)).symm

end

end FieldExtension
