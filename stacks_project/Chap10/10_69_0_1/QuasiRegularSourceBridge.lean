/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import stacks_project.Chap10.«10_69_0_1».QuasiRegularMonomialAction

@[expose] public section

open Polynomial
open scoped BigOperators TensorProduct Pointwise

universe u v

noncomputable section

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

theorem quasiRegularAssociatedGradedDegreeZeroInclusion_map_add
    (rs : List R)
    (x y : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) (x + y)) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) x) +
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) y) := by
  -- Compose additivity of the degree-zero monomial map with additivity of `DirectSum.lof`.
  rw [(quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)).map_add]
  exact (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
    (QuasiRegular.internalPiece (M := M) rs) 0).map_add _ _

-- TODO(10.69.0.1): show the degree-zero inclusion is quotient-linear over `R / J`; the current
-- failure is a scalar-compatibility elaboration issue for `map_smul_of_tower`.
theorem quasiRegularAssociatedGradedDegreeZeroInclusion_map_smul
    (rs : List R) (a : R ⧸ Ideal.ofList rs)
    (x : M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M)) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) (a • x)) =
      a • DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) x) := sorry

/-- The degree-zero inclusion `M / J M → ⊕_{n ≥ 0} J^n M / J^(n + 1) M`. -/
def quasiRegularAssociatedGradedDegreeZeroInclusion (rs : List R) :
    M ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R M) →ₗ[R ⧸ Ideal.ofList rs]
      QuasiRegular.internal (M := M) rs :=
  { toFun := fun x ↦
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs) 0
        (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ) x)
    map_add' := quasiRegularAssociatedGradedDegreeZeroInclusion_map_add rs
    map_smul' := quasiRegularAssociatedGradedDegreeZeroInclusion_map_smul rs }

/-- Helper for 10.69.0.1: the zero-exponent monomial class is represented by the obvious stage-zero
quotient class. -/
theorem quasiRegularAssociatedGradedInternalMonomialClass_zero_eq_mk
    (rs : List R) (m : M) :
    quasiRegularAssociatedGradedInternalMonomialClass rs m (0 : Fin rs.length →₀ ℕ) =
      Submodule.Quotient.mk
        ((⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩ : quasiRegularStage rs M 0)) := by
  -- Rewrite the zero monomial weight to `1`, so the two stage-zero representatives agree.
  rw [quasiRegularAssociatedGradedInternalMonomialClass]
  change
    (Submodule.Quotient.mk
      ((⟨quasiRegularAssociatedGradedMonomialWeight rs (0 : Fin rs.length →₀ ℕ) • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem rs
          (0 : Fin rs.length →₀ ℕ) m⟩ :
        quasiRegularStage rs M 0)) :
      QuasiRegular.internalPiece (M := M) rs 0) =
      Submodule.Quotient.mk
        ((⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩ : quasiRegularStage rs M 0))
  simp [quasiRegularAssociatedGradedMonomialWeight]

/-- Helper for 10.69.0.1: transporting a stage element along an equality of degrees does not
change its underlying module element. -/
theorem quasiRegularStage_cast_coe
    (rs : List R) {n n' : ℕ} (h : n = n')
    (x : quasiRegularStage rs M n) :
    (((cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x :
      quasiRegularStage rs M n') : M)) = x := by
  cases h
  rfl

/-- Helper for 10.69.0.1: quotienting commutes with transport between equal-degree internal
pieces. -/
theorem quasiRegularAssociatedGradedInternalPiece_cast_mk
    (rs : List R) {n n' : ℕ} (h : n = n')
    (x : quasiRegularStage rs M n) :
    (Submodule.Quotient.mk
      (cast (congrArg (fun k ↦ ↥(quasiRegularStage rs M k)) h) x) :
      QuasiRegular.internalPiece (M := M) rs n') =
      cast (congrArg (QuasiRegular.internalPiece (M := M) rs) h)
        (Submodule.Quotient.mk x : QuasiRegular.internalPiece (M := M) rs n) := by
  cases h
  rfl

/-- Helper for 10.69.0.1: `DirectSum.lof` is unchanged by transporting the homogeneous piece along
an equality of degrees. -/
theorem quasiRegularAssociatedGraded_lof_cast
    (rs : List R) {n n' : ℕ} (h : n = n')
    (z : QuasiRegular.internalPiece (M := M) rs n) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (QuasiRegular.internalPiece (M := M) rs) n'
      (cast (congrArg (QuasiRegular.internalPiece (M := M) rs) h) z) =
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (QuasiRegular.internalPiece (M := M) rs) n z := by
  cases h
  rfl

/-- Helper for 10.69.0.1: the explicit stage-zero monomial representative transports along
`|e| = 0 + |e|` to the usual representative in degree `|e|`. -/
theorem quasiRegularAssociatedGradedMonomialRepresentative_cast_zero_add
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
      quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs 0 e
        ⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩⟩ :
      quasiRegularStage rs M (0 + quasiRegularTotalDegree e)) =
      cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n))
        (QuasiRegular.monomialDegree_zero_add e))
        (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
          quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
          quasiRegularStage rs M (quasiRegularTotalDegree e)) := by
  -- A single named equality keeps all dependent stage casts on the canonical normalization path.
  let h := QuasiRegular.monomialDegree_zero_add e
  apply Subtype.ext
  change
    quasiRegularAssociatedGradedMonomialWeight rs e • m =
      ↑(cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n)) h)
        (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
          quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
          quasiRegularStage rs M (quasiRegularTotalDegree e)))
  exact
    (quasiRegularStage_cast_coe (M := M) rs h
      (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
          quasiRegularStage rs M (quasiRegularTotalDegree e))).symm

/-- Helper for 10.69.0.1: the quotient class coming from the stage-zero computation is the usual
monomial class after transporting the target degree from `|e|` to `0 + |e|`. -/
theorem quasiRegularAssociatedGradedInternalMonomialClass_cast_zero_add
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    (Submodule.Quotient.mk
      (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs 0 e
          ⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩⟩ :
        quasiRegularStage rs M (0 + quasiRegularTotalDegree e)) :
      QuasiRegular.internalPiece (M := M) rs (0 + quasiRegularTotalDegree e)) =
      (cast (congrArg (QuasiRegular.internalPiece (M := M) rs)
        (QuasiRegular.monomialDegree_zero_add e))
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e)) := by
  -- Reuse the canonical degree normalization so the quotient and stage casts share one path.
  let h := QuasiRegular.monomialDegree_zero_add e
  calc
    (Submodule.Quotient.mk
      (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
        quasiRegularAssociatedGradedMonomialWeight_smul_mem_stage rs 0 e
          ⟨m, quasiRegularStage_zero_mem (M := M) rs m⟩⟩ :
        quasiRegularStage rs M (0 + quasiRegularTotalDegree e)) :
      QuasiRegular.internalPiece (M := M) rs (0 + quasiRegularTotalDegree e)) =
      (Submodule.Quotient.mk
        (cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n))
          h
          )
          (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
            quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
            quasiRegularStage rs M (quasiRegularTotalDegree e))) :
        QuasiRegular.internalPiece (M := M) rs (0 + quasiRegularTotalDegree e)) := by
          simpa using congrArg
            (fun x : quasiRegularStage rs M (0 + quasiRegularTotalDegree e) ↦
              (Submodule.Quotient.mk x :
                QuasiRegular.internalPiece (M := M) rs
                  (0 + quasiRegularTotalDegree e)))
            (quasiRegularAssociatedGradedMonomialRepresentative_cast_zero_add
              (M := M) rs m e)
    _ =
      cast (congrArg (QuasiRegular.internalPiece (M := M) rs)
        h)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
          change
            (Submodule.Quotient.mk
              (cast (congrArg (fun n ↦ ↥(quasiRegularStage rs M n)) h)
                (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
                  quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
                  quasiRegularStage rs M (quasiRegularTotalDegree e))) :
              QuasiRegular.internalPiece (M := M) rs (0 + quasiRegularTotalDegree e)) =
            cast (congrArg (QuasiRegular.internalPiece (M := M) rs) h)
              (Submodule.Quotient.mk
                (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
                  quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
                  quasiRegularStage rs M (quasiRegularTotalDegree e)) :
                QuasiRegular.internalPiece (M := M) rs (quasiRegularTotalDegree e))
          exact
            quasiRegularAssociatedGradedInternalPiece_cast_mk (M := M) rs h
              (⟨quasiRegularAssociatedGradedMonomialWeight rs e • m,
                quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ :
                  quasiRegularStage rs M (quasiRegularTotalDegree e))

/-- Helper for 10.69.0.1: the homogeneous generator `DirectSum.lof` ignores the normalization
transport from `|e|` to `0 + |e|`. -/
theorem quasiRegularAssociatedGraded_lof_cast_zero_add
    (rs : List R) (e : Fin rs.length →₀ ℕ)
    (z : QuasiRegular.internalPiece (M := M) rs (quasiRegularTotalDegree e)) :
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (QuasiRegular.internalPiece (M := M) rs)
      (0 + quasiRegularTotalDegree e)
      ((cast (congrArg (QuasiRegular.internalPiece (M := M) rs)
        (QuasiRegular.monomialDegree_zero_add e)) z)) =
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (QuasiRegular.internalPiece (M := M) rs)
      (quasiRegularTotalDegree e) z := by
  -- Keep the direct-sum transport tied to the same canonical degree equality.
  let h := QuasiRegular.monomialDegree_zero_add e
  change
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (QuasiRegular.internalPiece (M := M) rs)
      (0 + quasiRegularTotalDegree e)
      (cast (congrArg (QuasiRegular.internalPiece (M := M) rs) h) z) =
    DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
      (QuasiRegular.internalPiece (M := M) rs)
      (quasiRegularTotalDegree e) z
  exact quasiRegularAssociatedGraded_lof_cast (M := M) rs h z

/-- Helper for 10.69.0.1: acting on the degree-zero monomial class computes the expected
representative-level monomial class, with the target index normalized from `0 + |e|` to `|e|`.
-/
theorem quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class_aux
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialMapOnPiece rs 0 e
        (quasiRegularAssociatedGradedInternalMonomialClass rs m (0 : Fin rs.length →₀ ℕ)) =
      (cast (congrArg (QuasiRegular.internalPiece (M := M) rs)
        (QuasiRegular.monomialDegree_zero_add e))
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e)) := sorry

-- Proof sketch: a monomial acts on the degree-zero piece by multiplication with the corresponding
-- monomial weight, landing in the graded piece indexed by its total degree.
/-- The action of a monomial on a degree-zero class is the expected class of the monomial-weighted
representative in the corresponding graded piece. -/
theorem quasiRegularAssociatedGradedMonomialAction_degreeZero_mk
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialAction rs e
        (quasiRegularAssociatedGradedDegreeZeroInclusion rs (Submodule.Quotient.mk m)) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs)
        (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
  -- Route correction: unfold the degree-zero inclusion to a homogeneous generator, compute the
  -- monomial action there, and only then normalize the final `DirectSum.lof` transport.
  calc
    quasiRegularAssociatedGradedMonomialAction rs e
        (quasiRegularAssociatedGradedDegreeZeroInclusion rs (Submodule.Quotient.mk m)) =
      quasiRegularAssociatedGradedMonomialAction rs e
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (QuasiRegular.internalPiece (M := M) rs) 0
          (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
            (Submodule.Quotient.mk m))) := by
          rfl
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs)
        (0 + quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedMonomialMapOnPiece rs 0 e
          (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
            (Submodule.Quotient.mk m))) := by
          -- Evaluate the monomial action on the degree-zero homogeneous generator.
          exact quasiRegularAssociatedGradedMonomialAction_lof
            (M := M) rs 0 e
            (quasiRegularAssociatedGradedMonomialMap rs (0 : Fin rs.length →₀ ℕ)
              (Submodule.Quotient.mk m))
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs)
        (0 + quasiRegularTotalDegree e)
        (cast (congrArg (QuasiRegular.internalPiece (M := M) rs)
          (by simpa using (Nat.zero_add (quasiRegularTotalDegree e))))
          (quasiRegularAssociatedGradedInternalMonomialClass rs m e)) := by
          -- Rewrite the inner degree-zero class using the stabilized quotient-level cast API.
          rw [quasiRegularAssociatedGradedMonomialMap_mk]
          rw [quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class_aux (M := M)]
    _ =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := M) rs)
        (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
          -- Normalize the target index from `0 + |e|` back to `|e|`.
          exact quasiRegularAssociatedGraded_lof_cast_zero_add (M := M) rs e
            (quasiRegularAssociatedGradedInternalMonomialClass rs m e)

/-- Stacks `061P`: the polynomial module on the left-oriented tensor source. -/
@[stacks 061P "left-oriented comparison source module"]
noncomputable abbrev quasiRegularSequenceAssociatedGradedSourceModule
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (TensorProduct (R ⧸ Ideal.ofList rs)
        (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
        (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N))) :=
  TensorProduct.leftModule

/-- Stacks `061P`: the polynomial module on the textbook right-oriented tensor source, shared with
`QuasiRegular.comparisonSourceModule`. -/
@[stacks 061P "right-oriented comparison source module"]
noncomputable abbrev quasiRegularSequenceAssociatedGradedTextbookSourceModule
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    Module (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      ((N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) ⊗[R ⧸ Ideal.ofList rs]
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :=
  QuasiRegular.comparisonSourceModule (M := N) rs

/-- Stacks `061P`: the canonical base-change map transported to the chapter's internal
associated-graded presentation.  The data owner is `QuasiRegular.baseChangeMap`. -/
@[stacks 061P "internal associated-graded base-change map"]
noncomputable abbrev quasiRegularSequenceAssociatedGradedMapAux
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    TensorProduct (R ⧸ Ideal.ofList rs)
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) →ₗ[
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      QuasiRegular.internal (M := N) rs :=
  (QuasiRegular.internalLinearEquiv (M := N) rs).toLinearMap.comp
    (QuasiRegular.baseChangeMap (M := N) rs)

/-- Helper for 10.69.0.1: on a monomial tensor in the base-change model, the auxiliary map is the
expected monomial action on the degree-zero class. -/
theorem quasiRegularSequenceAssociatedGradedMapAux_tmul_monomial
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (m : N) (e : Fin rs.length →₀ ℕ) :
    quasiRegularSequenceAssociatedGradedMapAux N rs
        ((MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) ⊗ₜ[R ⧸ Ideal.ofList rs]
          Submodule.Quotient.mk m) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (QuasiRegular.internalPiece (M := N) rs)
        (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := sorry

/-- The tensor-commutation map from the textbook source
`M / J M ⊗_{R / J} (R / J)[X₁, ..., X_c]` to the base-change source
`(R / J)[X₁, ..., X_c] ⊗_{R / J} M / J M`.

This chapter name is a reducible view of the ReasLib comparison-source owner; the module
instances are deliberately shared so downstream linear maps remain definitionally compatible. -/
noncomputable abbrev quasiRegularSequenceAssociatedGradedSourceComm
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R) :
    ((N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) ⊗[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) →ₗ[
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)]
      TensorProduct (R ⧸ Ideal.ofList rs)
        (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
        (N ⧸ ((Ideal.ofList rs) • ⊤ : Submodule R N)) :=
  QuasiRegular.comparisonSourceComm (M := N) rs

/-- Helper for 10.69.0.1: the source commutation map swaps a quotient representative and a
monomial simple tensor in the textbook tensor-product source. -/
theorem quasiRegularSequenceAssociatedGradedSourceComm_tmul
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (m : N) (e : Fin rs.length →₀ ℕ) :
    quasiRegularSequenceAssociatedGradedSourceComm N rs
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) =
      (MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs)) ⊗ₜ[R ⧸ Ideal.ofList rs]
        Submodule.Quotient.mk m := by
  simpa using QuasiRegular.comparisonSourceComm_tmul (M := N) rs m
    (MvPolynomial.monomial e (1 : R ⧸ Ideal.ofList rs))

/-- Helper for 10.69.0.1: the internal-model piece equivalence sends the monomial class to the
textbook quotient class represented by the same weighted element. -/
theorem quasiRegularAssociatedGradedInternalPieceEquiv_monomialClass
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (m : N) (e : Fin rs.length →₀ ℕ) :
    QuasiRegular.internalPieceEquiv (M := N) rs (quasiRegularTotalDegree e)
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) =
      Submodule.Quotient.mk
        ⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m, by
          simpa [quasiRegularAssociatedGradedMonomialWeight] using
            quasiRegularAssociatedGradedMonomialWeight_smul_mem rs e m⟩ := by
  -- The piece equivalence is `quotEquivOfEq`, so it preserves quotient representatives verbatim.
  rw [QuasiRegular.internalPieceEquiv,
    quasiRegularAssociatedGradedInternalMonomialClass]
  exact Submodule.quotEquivOfEq_mk
    (((quasiRegularIdeal rs) • ⊤ :
      Submodule R (Ideal.AssociatedGraded.stage (quasiRegularIdeal rs) N (quasiRegularTotalDegree e))))
    (((Ideal.AssociatedGraded.stage (quasiRegularIdeal rs) N (quasiRegularTotalDegree e + 1)).submoduleOf
      (Ideal.AssociatedGraded.stage (quasiRegularIdeal rs) N (quasiRegularTotalDegree e)))) _ _

/-- Helper for 10.69.0.1: the inverse direct-sum equivalence sends a homogeneous generator to the
same homogeneous generator with the componentwise piece equivalence applied. -/
theorem quasiRegularAssociatedGradedAddEquiv_symm_lof
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (n : ℕ) (z : QuasiRegular.internalPiece (M := N) rs n) :
    (QuasiRegular.internalAddEquiv (M := N) rs).symm
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (QuasiRegular.internalPiece (M := N) rs) n z) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (Ideal.AssociatedGraded.piece (Ideal.ofList rs) N) n
        (QuasiRegular.internalPieceEquiv (M := N) rs n z) := by
  -- This is the single-support case of the direct-sum congruence attached to the piecewise
  -- quotient equivalences.
  change DirectSum.map
      (fun k ↦ (QuasiRegular.internalPieceEquiv (M := N) rs k).toAddMonoidHom)
      (DirectSum.of (QuasiRegular.internalPiece (M := N) rs) n z) =
    DirectSum.of (Ideal.AssociatedGraded.piece (Ideal.ofList rs) N) n
      (QuasiRegular.internalPieceEquiv (M := N) rs n z)
  -- Now this is exactly the `DirectSum.map` formula on a single homogeneous generator.
  simpa using DirectSum.map_of
    (f := fun k ↦ (QuasiRegular.internalPieceEquiv (M := N) rs k).toAddMonoidHom)
    n z

/-- Helper for 10.69.0.1: acting on the degree-zero monomial class computes the expected
representative-level monomial class. -/
theorem quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class
    (rs : List R) (m : M) (e : Fin rs.length →₀ ℕ) :
    quasiRegularAssociatedGradedMonomialMapOnPiece rs 0 e
        (quasiRegularAssociatedGradedInternalMonomialClass rs m (0 : Fin rs.length →₀ ℕ)) =
      cast
        (congrArg (QuasiRegular.internalPiece (M := M) rs)
          (by simpa using (Nat.zero_add (quasiRegularTotalDegree e))))
        (quasiRegularAssociatedGradedInternalMonomialClass rs m e) := by
  -- Reuse the earlier normalized representative computation for the degree-zero source class.
  exact quasiRegularAssociatedGradedMonomialMapOnPiece_zero_class_aux
    (M := M) rs m e

/-- Helper for 10.69.0.1: transporting one homogeneous generator through the direct-sum
identification from the internal quotient model to the textbook graded piece only applies the
piecewise equivalence. -/
theorem quasiRegularAssociatedGradedAddEquiv_lof
    (N : Type v) [AddCommGroup N] [Module R N] (rs : List R)
    (n : ℕ) (z : QuasiRegular.internalPiece (M := N) rs n) :
    ((QuasiRegular.internalAddEquiv (M := N) rs).linearEquiv
      (R ⧸ Ideal.ofList rs)).symm
        (DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
          (QuasiRegular.internalPiece (M := N) rs) n z) =
      DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
        (Ideal.AssociatedGraded.piece (Ideal.ofList rs) N) n
        (QuasiRegular.internalPieceEquiv (M := N) rs n z) := by
  -- The transferred linear equivalence has the same underlying function as the additive one.
  simpa using quasiRegularAssociatedGradedAddEquiv_symm_lof
    (N := N) rs n z

#check @QuasiRegular.internalAddEquiv_map_smul
#check @QuasiRegular.internalLinearEquiv
#check @quasiRegularSequenceAssociatedGradedMapAux
#check @quasiRegularSequenceAssociatedGradedSourceComm
#check @QuasiRegular.baseChangeMap
#check @QuasiRegular.comparisonSourceComm

end RingTheory.Sequence

end
