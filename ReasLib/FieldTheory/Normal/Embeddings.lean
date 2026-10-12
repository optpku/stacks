/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

namespace FieldExtension

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/-- An algebraic extension is normal exactly when all embeddings into
an algebraic closure have the same image intermediate field. -/
theorem normal_iff_forall_algHom_fieldRange_eq :
    Normal F E ↔
      ∀ σ σ' : E →ₐ[F] AlgebraicClosure F, σ.fieldRange = σ'.fieldRange := by
  let ι : E →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  let e : E ≃ₐ[F] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  constructor
  · intro h σ σ'
    have hι (τ : E →ₐ[F] AlgebraicClosure F) : τ.fieldRange = ι.fieldRange := by
      -- Local instance justification (proof-local temporary data): transport normality across the chosen equivalence from `E` to its image field in the algebraic closure.
      letI : Normal F ι.fieldRange := e.transfer_normal.1 h
      have hcomp :
          IntermediateField.map τ ((e.symm : ι.fieldRange →ₐ[F] E).fieldRange) =
            (τ.comp e.symm.toAlgHom).fieldRange := by
        simpa using AlgHom.map_fieldRange e.symm.toAlgHom τ
      have htop : (e.symm : ι.fieldRange →ₐ[F] E).fieldRange = ⊤ :=
        AlgEquiv.fieldRange_eq_top e.symm
      calc
        τ.fieldRange = IntermediateField.map τ ⊤ := AlgHom.fieldRange_eq_map τ
        _ = IntermediateField.map τ ((e.symm : ι.fieldRange →ₐ[F] E).fieldRange) := by
          rw [htop]
        _ = (τ.comp e.symm.toAlgHom).fieldRange := hcomp
        _ = ι.fieldRange := AlgHom.fieldRange_of_normal (τ.comp e.symm.toAlgHom)
    exact (hι σ).trans (hι σ').symm
  · intro h
    have hfieldRange (τ : ι.fieldRange →ₐ[F] AlgebraicClosure F) :
        τ.fieldRange = ι.fieldRange := by
      have hcomp :
          IntermediateField.map τ ((e : E →ₐ[F] ι.fieldRange).fieldRange) =
            (τ.comp e.toAlgHom).fieldRange := by
        simpa using AlgHom.map_fieldRange e.toAlgHom τ
      have htop : (e : E →ₐ[F] ι.fieldRange).fieldRange = ⊤ := AlgEquiv.fieldRange_eq_top e
      calc
        τ.fieldRange = IntermediateField.map τ ⊤ := AlgHom.fieldRange_eq_map τ
        _ = IntermediateField.map τ ((e : E →ₐ[F] ι.fieldRange).fieldRange) := by
          rw [htop]
        _ = (τ.comp e.toAlgHom).fieldRange := hcomp
        _ = ι.fieldRange := h (τ.comp e.toAlgHom) ι
    exact e.transfer_normal.2 <| IntermediateField.normal_iff_forall_fieldRange_eq.2 hfieldRange

end

section

variable {K : Type u} {M : Type v} {L : Type w}
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L]

/-- The canonical automorphism of a normal target extending a given map into that target. -/
noncomputable def galExtensionOfAlgHom [Normal K L] (σ : M →ₐ[K] L) : Gal(L/K) :=
  AlgEquiv.ofBijective (σ.liftNormal L) (AlgHom.normal_bijective K L L _)

/-- `galExtensionOfAlgHom σ` extends `σ` along the scalar-tower map from `M` to `L`. -/
theorem galExtensionOfAlgHom_comp [Normal K L] (σ : M →ₐ[K] L) :
    (galExtensionOfAlgHom σ).toAlgHom.comp (IsScalarTower.toAlgHom K M L) = σ := by
  ext x
  exact σ.liftNormal_commutes L x

/-- Every map into a normal extension extends to an automorphism of
that normal extension. -/
theorem existsGalExtendingAlgHom [Normal K L] (σ : M →ₐ[K] L) :
    ∃ τ : Gal(L/K), τ.toAlgHom.comp (IsScalarTower.toAlgHom K M L) = σ :=
  ⟨galExtensionOfAlgHom σ, galExtensionOfAlgHom_comp σ⟩

end

end FieldExtension
