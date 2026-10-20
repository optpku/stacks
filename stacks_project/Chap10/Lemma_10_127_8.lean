/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation.Isomorphism
public import ReasLib.RingTheory.DirectLimit.Algebra.Tensor
public import ReasLib.RingTheory.DirectLimit.Comparison

@[expose] public section

/-!
# Finite-presentation descent along a directed colimit

@stack 05N9

The canonical tensor and finite-presentation descent primitives live in
`Ring.DirectLimit`.  This file retains the three source-facing algebra
statements for a chosen identification of a ring direct limit with `R`.
-/

open scoped TensorProduct

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {Λ : Type v} [Preorder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
variable (RStage : Λ → Type u) [∀ i, CommRing (RStage i)]
variable (map : ∀ i j, i ≤ j → RStage i →+* RStage j)
variable [DirectedSystem RStage (fun i j h ↦ map i j h)]
variable (colimitIso : Ring.DirectLimit RStage (fun i j h ↦ map i j h) ≃+* R)

#check @Ring.DirectLimit.exists_stageTensorMap
#check @Ring.DirectLimit.eventuallyEqStageTensorMap
#check @Ring.DirectLimit.Algebra.BaseChange.FinitePresentation.Isomorphism.exists_stage

/-- Lemma 10.127.8 (1): every finitely presented `R`-algebra is obtained by base change from a
finitely presented algebra over some stage of a directed colimit presentation of `R`.

The descended algebra is produced in `Type u`, the universe of the stages, where a finite
presentation model canonically lives. -/
@[stacks 05N9]
theorem finitelyPresented_algebra_is_baseChange_of_stage
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : Λ) (A_i : Type u) (_ : CommRing A_i) (_ : Algebra (RStage i) A_i)
      (_ : Algebra.FinitePresentation (RStage i) A_i),
      letI : Algebra (RStage i) R :=
        (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      letI : Algebra R (A_i ⊗[RStage i] R) := Algebra.TensorProduct.rightAlgebra
      Nonempty (A_i ⊗[RStage i] R ≃ₐ[R] A) := sorry

/-- Lemma 10.127.8 (2): a map from a finitely presented stage algebra into a limit base change
descends to a base change over some later stage. -/
@[stacks 05N9]
theorem finitePresentation_hom_to_limit_baseChange_descends {i : Λ}
    (A_i : Type w) [CommRing A_i] [Algebra (RStage i) A_i]
    [Algebra.FinitePresentation (RStage i) A_i]
    (B_i : Type w) [CommRing B_i] [Algebra (RStage i) B_i]
    [Algebra.FinitePresentation (RStage i) B_i]
    (φ :
      letI : Algebra (RStage i) R :=
        (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      A_i →ₐ[RStage i] B_i ⊗[RStage i] R) :
    ∃ (j : Λ) (hij : i ≤ j),
      letI : Algebra (RStage i) (RStage j) := (map i j hij).toAlgebra
      letI : Algebra (RStage i) R :=
        (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      letI : Algebra (RStage j) R :=
        (Ring.DirectLimit.toLimitHom RStage map colimitIso j).toAlgebra
      letI : IsScalarTower (RStage i) (RStage j) R :=
        Ring.DirectLimit.toLimit_isScalarTower RStage map colimitIso hij
      ∃ φ_j : A_i →ₐ[RStage i] B_i ⊗[RStage i] RStage j,
        (Algebra.TensorProduct.map (AlgHom.id (RStage i) B_i)
          (IsScalarTower.toAlgHom (RStage i) (RStage j) R)).comp φ_j = φ := sorry

/-- Lemma 10.127.8 (3): equality of two maps after base change to the colimit ring is already
witnessed after base change to some later stage. -/
@[stacks 05N9]
theorem finitePresentation_map_equality_stabilizes {i : Λ}
    (A_i : Type w) [CommRing A_i] [Algebra (RStage i) A_i]
    [Algebra.FinitePresentation (RStage i) A_i]
    (B_i : Type w) [CommRing B_i] [Algebra (RStage i) B_i]
    [Algebra.FinitePresentation (RStage i) B_i]
    (φ ψ : A_i →ₐ[RStage i] B_i)
    (hφψ :
      letI : Algebra (RStage i) R :=
        (Ring.DirectLimit.toLimitHom RStage map colimitIso i).toAlgebra
      Algebra.TensorProduct.map φ (AlgHom.id (RStage i) R) =
        Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) R)) :
    ∃ (j : Λ) (hij : i ≤ j),
      letI : Algebra (RStage i) (RStage j) := (map i j hij).toAlgebra
      Algebra.TensorProduct.map φ (AlgHom.id (RStage i) (RStage j)) =
        Algebra.TensorProduct.map ψ (AlgHom.id (RStage i) (RStage j)) := sorry

end
