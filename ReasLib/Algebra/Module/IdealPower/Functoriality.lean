/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Hom

/-!
# Functoriality of ideal-power torsion quotients and Hom systems

This file supplies the maps induced by a linear map on the quotients by
ideal-power annihilated submodules, and packages them into maps of the
quotient Hom direct systems.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- A linear map sends the `I ^ n`-annihilated submodule of its source into the corresponding
submodule of its target. -/
theorem powerAnnihilatedSubmodule_le_comap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerAnnihilatedSubmodule M n ≤
      (I.powerAnnihilatedSubmodule N n).comap f := sorry

/-- The map on quotients by the `I ^ n`-annihilated submodules induced by a linear map. -/
noncomputable def powerAnnihilatedQuotientMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    M ⧸ I.powerAnnihilatedSubmodule M n →ₗ[R]
      N ⧸ I.powerAnnihilatedSubmodule N n :=
  Submodule.mapQ
    (I.powerAnnihilatedSubmodule M n)
    (I.powerAnnihilatedSubmodule N n)
    f
    (I.powerAnnihilatedSubmodule_le_comap f n)

/-- The ideal-power torsion quotient map sends the class of `x` to the class of `f x`. -/
@[simp]
theorem powerAnnihilatedQuotientMap_apply_mkQ (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (x : M) :
    I.powerAnnihilatedQuotientMap f n
        ((I.powerAnnihilatedSubmodule M n).mkQ x) =
      (I.powerAnnihilatedSubmodule N n).mkQ (f x) := sorry

/-- The quotient map induced by an identity linear map is the identity. -/
@[simp]
theorem powerAnnihilatedQuotientMap_id (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    I.powerAnnihilatedQuotientMap (LinearMap.id : M →ₗ[R] M) n = LinearMap.id := sorry

/-- Quotient maps induced by linear maps preserve composition. -/
theorem powerAnnihilatedQuotientMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    I.powerAnnihilatedQuotientMap (g.comp f) n =
      (I.powerAnnihilatedQuotientMap g n).comp (I.powerAnnihilatedQuotientMap f n) := sorry

/-- Postcomposition on quotient ideal-power Hom modules. -/
noncomputable def powerQuotientHomMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerQuotientHom M n →ₗ[R] I.powerQuotientHom N n :=
  LinearMap.compRight R (I.powerAnnihilatedQuotientMap f n)

/-- Postcomposition on quotient ideal-power Hom modules sends `φ` to the quotient map composed
with `φ`. -/
@[simp]
theorem powerQuotientHomMap_apply (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (φ : I.powerQuotientHom M n) :
    I.powerQuotientHomMap f n φ =
      (I.powerAnnihilatedQuotientMap f n).comp φ := sorry

/-- Postcomposition by the identity is the identity on a quotient ideal-power Hom module. -/
@[simp]
theorem powerQuotientHomMap_id (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) :
    I.powerQuotientHomMap (LinearMap.id : M →ₗ[R] M) n = LinearMap.id := sorry

/-- Postcomposition on quotient ideal-power Hom modules preserves composition. -/
theorem powerQuotientHomMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    I.powerQuotientHomMap (g.comp f) n =
      (I.powerQuotientHomMap g n).comp (I.powerQuotientHomMap f n) := sorry

/-- The additive-group map on a quotient ideal-power Hom stage induced by a linear map. -/
noncomputable def powerQuotientHomStageMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerQuotientHomStage M n ⟶ I.powerQuotientHomStage N n :=
  AddCommGrpCat.ofHom (I.powerQuotientHomMap f n).toAddMonoidHom

/-- The quotient ideal-power Hom stage map induced by the identity is the identity. -/
@[simp]
theorem powerQuotientHomStageMap_id (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) :
    I.powerQuotientHomStageMap (LinearMap.id : M →ₗ[R] M) n = 𝟙 _ := sorry

/-- Quotient ideal-power Hom stage maps induced by linear maps preserve composition. -/
theorem powerQuotientHomStageMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    I.powerQuotientHomStageMap (g.comp f) n =
      I.powerQuotientHomStageMap f n ≫ I.powerQuotientHomStageMap g n := sorry

/-- Quotient ideal-power Hom stage maps commute with direct-system transitions. -/
theorem powerQuotientHomStageMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerQuotientHomTransition M n ≫ I.powerQuotientHomStageMap f (n + 1) =
      I.powerQuotientHomStageMap f n ≫ I.powerQuotientHomTransition N n := sorry

/-- The successor naturality condition for the quotient ideal-power Hom diagram maps. -/
theorem powerQuotientHomDiagramMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerQuotientHomDiagram M).map (homOfLE (Nat.le_succ n)) ≫
        I.powerQuotientHomStageMap f (n + 1) =
      I.powerQuotientHomStageMap f n ≫
        (I.powerQuotientHomDiagram N).map (homOfLE (Nat.le_succ n)) := sorry

/-- The natural transformation between quotient ideal-power Hom diagrams induced by a linear map. -/
noncomputable def powerQuotientHomDiagramMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    I.powerQuotientHomDiagram M ⟶ I.powerQuotientHomDiagram N :=
  NatTrans.ofSequence
    (fun n ↦ I.powerQuotientHomStageMap f n)
    (I.powerQuotientHomDiagramMap_naturality f)

/-- The component of `powerQuotientHomDiagramMap` at `n` is its quotient Hom stage map. -/
@[simp]
theorem powerQuotientHomDiagramMap_app (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerQuotientHomDiagramMap f).app n = I.powerQuotientHomStageMap f n := sorry

/-- The quotient ideal-power Hom diagram map induced by the identity is the identity natural
transformation. -/
@[simp]
theorem powerQuotientHomDiagramMap_id (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    I.powerQuotientHomDiagramMap (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := sorry

/-- Quotient ideal-power Hom diagram maps induced by linear maps preserve composition. -/
theorem powerQuotientHomDiagramMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    I.powerQuotientHomDiagramMap (g.comp f) =
      I.powerQuotientHomDiagramMap f ≫ I.powerQuotientHomDiagramMap g := sorry

end Ideal

