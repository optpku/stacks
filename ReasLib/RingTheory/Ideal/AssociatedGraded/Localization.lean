/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import ReasLib.Algebra.Module.LocalizedModule.Quotient
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

/-!
# Localization of associated graded modules

Localization commutes with the stages, pieces, and direct-sum module of the
`I`-adic associated graded construction. The API is stated for an arbitrary
ideal; sequence ideals are a downstream specialization via `Ideal.map_ofList`.
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Localization carries the `n`-th `I`-adic stage to the `n`-th stage for the mapped ideal. -/
@[stacks 061Q "localized associated graded stage"]
theorem localizedStage_eq (I : Ideal R) (S : Submonoid R) (n : ℕ) :
    (stage I M n).localized S =
      stage (I.map (algebraMap R (Localization S))) (LocalizedModule S M) n := sorry

/-- The canonical linear equivalence between the localization of an `I`-adic stage and the
corresponding stage of the localized module. -/
@[stacks 061Q "localized associated graded stage equivalence"]
noncomputable def localizedStageEquiv (I : Ideal R) (S : Submonoid R) (n : ℕ) :
    LocalizedModule S (stage I M n) ≃ₗ[Localization S]
      stage (I.map (algebraMap R (Localization S))) (LocalizedModule S M) n :=
  ((stage I M n).localizedEquiv S).symm.trans
    (LinearEquiv.ofEq _ _ (localizedStage_eq (M := M) I S n))

/-- The localized-stage equivalence sends a denominator-one stage element to its image in the
ambient localized module. -/
@[simp, stacks 061Q "localized associated graded stage generator"]
theorem localizedStageEquiv_mk
    (I : Ideal R) (S : Submonoid R) (n : ℕ) (x : stage I M n) :
    ((localizedStageEquiv (M := M) I S n
        (LocalizedModule.mkLinearMap S (stage I M n) x) :
      stage (I.map (algebraMap R (Localization S))) (LocalizedModule S M) n) :
        LocalizedModule S M) =
      LocalizedModule.mkLinearMap S M x := sorry

/-- The localized-stage equivalence carries the localized quotient denominator to the quotient
denominator for the mapped ideal. -/
theorem localizedStageEquiv_map_denominator
    (I : Ideal R) (S : Submonoid R) (n : ℕ) :
    Submodule.map
        (localizedStageEquiv (M := M) I S n).toLinearMap
        ((denominator I M n).localized S) =
      denominator (I.map (algebraMap R (Localization S))) (LocalizedModule S M) n := sorry

/-- The localization of an associated graded piece is canonically the corresponding piece for
the mapped ideal acting on the localized module. -/
@[stacks 061Q "localized associated graded piece"]
noncomputable def localizedPieceEquiv (I : Ideal R) (S : Submonoid R) (n : ℕ) :
    LocalizedModule S (piece I M n) ≃ₗ[Localization S]
      piece (I.map (algebraMap R (Localization S))) (LocalizedModule S M) n :=
  (localizedQuotientEquiv S (denominator I M n)).symm.trans
    (Submodule.Quotient.equiv
      ((denominator I M n).localized S)
      (denominator (I.map (algebraMap R (Localization S))) (LocalizedModule S M) n)
      (localizedStageEquiv (M := M) I S n)
      (localizedStageEquiv_map_denominator (M := M) I S n))

/-- The localized-piece equivalence sends the denominator-one class of a stage element to the
corresponding class of its localized stage element. -/
@[simp, stacks 061Q "localized associated graded piece generator"]
theorem localizedPieceEquiv_mk
    (I : Ideal R) (S : Submonoid R) (n : ℕ) (x : stage I M n) :
    localizedPieceEquiv (M := M) I S n
        (LocalizedModule.mkLinearMap S (piece I M n) (Submodule.Quotient.mk x)) =
      (Submodule.Quotient.mk
        (localizedStageEquiv (M := M) I S n
          (LocalizedModule.mkLinearMap S (stage I M n) x)) :
        piece (I.map (algebraMap R (Localization S))) (LocalizedModule S M) n) := sorry

/-- The degreewise localization map from an associated graded module to the associated graded
module of the localization. -/
@[stacks 061Q "associated graded localization map"]
noncomputable def localizationMap (I : Ideal R) (S : Submonoid R) :
    gradedModule I M →ₗ[R]
      gradedModule (I.map (algebraMap R (Localization S))) (LocalizedModule S M) :=
  DirectSum.lmap fun n ↦
    (LinearMap.restrictScalars R
      (localizedPieceEquiv (M := M) I S n).toLinearMap).comp
        (LocalizedModule.mkLinearMap S (piece I M n))

/-- The degreewise associated graded localization map is a base-change map. -/
@[stacks 061Q "associated graded localization is base change"]
theorem localizationMap_isBaseChange (I : Ideal R) (S : Submonoid R) :
    IsBaseChange (Localization S) (localizationMap (M := M) I S) := sorry

/-- Localization commutes canonically with the entire associated graded module. -/
@[stacks 061Q "localized associated graded module"]
noncomputable def localizedGradedModuleEquiv (I : Ideal R) (S : Submonoid R) :
    LocalizedModule S (gradedModule I M) ≃ₗ[Localization S]
      gradedModule (I.map (algebraMap R (Localization S))) (LocalizedModule S M) :=
  (LocalizedModule.equivTensorProduct S (gradedModule I M)).trans
    (localizationMap_isBaseChange (M := M) I S).equiv

/-- The associated graded localization equivalence acts degreewise on denominator-one homogeneous
elements. -/
@[simp, stacks 061Q "localized associated graded homogeneous generator"]
theorem localizedGradedModuleEquiv_mk_lof
    (I : Ideal R) (S : Submonoid R) (n : ℕ) (z : piece I M n) :
    localizedGradedModuleEquiv (M := M) I S
        (LocalizedModule.mkLinearMap S (gradedModule I M)
          (DirectSum.lof R ℕ (piece I M) n z)) =
      DirectSum.lof (Localization S) ℕ
        (piece (I.map (algebraMap R (Localization S))) (LocalizedModule S M)) n
        (localizedPieceEquiv (M := M) I S n
          (LocalizedModule.mkLinearMap S (piece I M n) z)) := sorry

end Ideal.AssociatedGraded
