/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Module.IdealPower.Functoriality

/-!
# Module-category ideal-power Hom systems

This leaf upgrades the additive direct systems from `IdealPower.Hom` to
`ModuleCat` when the coefficient ring is a commutative ring.  The additive
systems remain the semiring-general core; this leaf is the stronger interface
for linear and categorical applications.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace Ideal

section HomSystem

variable {R : Type u} [CommRing R]

/-- The `n`-th ideal-power Hom module as an object of `ModuleCat R`. -/
noncomputable abbrev powerHomModuleStage (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (I.powerHom M n)

/-- Restriction along `I^(n + 1) ≤ I^n` as a morphism of `R`-modules. -/
noncomputable def powerHomModuleTransition (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] (n : ℕ) :
    I.powerHomModuleStage M n ⟶ I.powerHomModuleStage M (n + 1) :=
  ModuleCat.ofHom
    (LinearMap.lcomp R M (Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ)))

/-- Applying the module-valued Hom transition restricts a map to `I^(n + 1)`. -/
@[simp]
theorem powerHomModuleTransition_apply (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] (n : ℕ) (φ : I.powerHom M n) :
    (I.powerHomModuleTransition M n).hom φ =
      φ.comp (Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ)) := sorry

/-- The `ModuleCat R` sequential diagram `n ↦ Hom_R(I^n, M)`. -/
noncomputable def powerHomModuleDiagram (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] : ℕ ⥤ ModuleCat.{max u v} R :=
  Functor.ofSequence (fun n ↦ I.powerHomModuleTransition M n)

/-- Postcomposition by a linear map as a morphism between ideal-power Hom module stages. -/
noncomputable def powerHomModuleStageMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerHomModuleStage M n ⟶ I.powerHomModuleStage N n :=
  ModuleCat.ofHom (I.powerHomMap f n)

/-- Applying a module-valued Hom stage map postcomposes with the given linear map. -/
@[simp]
theorem powerHomModuleStageMap_apply (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (φ : I.powerHom M n) :
    (I.powerHomModuleStageMap f n).hom φ = f.comp φ := sorry

/-- The module-stage maps commute with ideal-power restriction transitions. -/
theorem powerHomModuleStageMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerHomModuleTransition M n ≫ I.powerHomModuleStageMap f (n + 1) =
      I.powerHomModuleStageMap f n ≫ I.powerHomModuleTransition N n := sorry

/-- The module-valued Hom stage map induced by the identity is the identity. -/
@[simp]
theorem powerHomModuleStageMap_id (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] (n : ℕ) :
    I.powerHomModuleStageMap (LinearMap.id : M →ₗ[R] M) n = 𝟙 _ := sorry

/-- Module-valued Hom stage maps preserve composition. -/
theorem powerHomModuleStageMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    I.powerHomModuleStageMap (g.comp f) n =
      I.powerHomModuleStageMap f n ≫ I.powerHomModuleStageMap g n := sorry

/-- The successor naturality condition for the module-valued ideal-power Hom diagrams. -/
theorem powerHomModuleDiagramMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerHomModuleDiagram M).map (homOfLE (Nat.le_succ n)) ≫
        I.powerHomModuleStageMap f (n + 1) =
      I.powerHomModuleStageMap f n ≫
        (I.powerHomModuleDiagram N).map (homOfLE (Nat.le_succ n)) := sorry

/-- The natural transformation between module-valued ideal-power Hom diagrams induced by
postcomposition with a linear map. -/
noncomputable def powerHomModuleDiagramMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    I.powerHomModuleDiagram M ⟶ I.powerHomModuleDiagram N :=
  NatTrans.ofSequence
    (fun n ↦ I.powerHomModuleStageMap f n)
    (I.powerHomModuleDiagramMap_naturality f)

/-- The component of `powerHomModuleDiagramMap` at `n` is the postcomposition stage map. -/
@[simp]
theorem powerHomModuleDiagramMap_app (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerHomModuleDiagramMap f).app n = I.powerHomModuleStageMap f n := sorry

/-- The module-valued ideal-power Hom diagram map induced by the identity is the identity. -/
@[simp]
theorem powerHomModuleDiagramMap_id (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] :
    I.powerHomModuleDiagramMap (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := sorry

/-- Module-valued ideal-power Hom diagram maps preserve composition. -/
theorem powerHomModuleDiagramMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    I.powerHomModuleDiagramMap (g.comp f) =
      I.powerHomModuleDiagramMap f ≫ I.powerHomModuleDiagramMap g := sorry

end HomSystem

section QuotientHomSystem

variable {R : Type u} [CommRing R]

/-- The `n`-th quotient ideal-power Hom module as an object of `ModuleCat R`. -/
noncomputable abbrev powerQuotientHomModuleStage (I : Ideal R) (M : Type v) [AddCommGroup M]
    [Module R M] (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (I.powerQuotientHom M n)

/-- The transition morphism in the module-valued quotient ideal-power Hom system. -/
noncomputable def powerQuotientHomModuleTransition (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    I.powerQuotientHomModuleStage M n ⟶ I.powerQuotientHomModuleStage M (n + 1) :=
  ModuleCat.ofHom
    ((LinearMap.compRight R (I.powerQuotientHomQuotientMap M n)).comp
      (LinearMap.lcomp R _ (I.powerQuotientHomRestriction n)))

/-- Applying the quotient module transition first restricts and then maps quotient classes. -/
@[simp]
theorem powerQuotientHomModuleTransition_apply (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) (φ : I.powerQuotientHom M n) :
    (I.powerQuotientHomModuleTransition M n).hom φ =
      (I.powerQuotientHomQuotientMap M n).comp
        (φ.comp (I.powerQuotientHomRestriction n)) := sorry

/-- The `ModuleCat R` sequential diagram `n ↦ Hom_R(I^n, M / M_n)`. -/
noncomputable def powerQuotientHomModuleDiagram (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℕ ⥤ ModuleCat.{max u v} R :=
  Functor.ofSequence (fun n ↦ I.powerQuotientHomModuleTransition M n)

/-- Postcomposition by a linear map as a morphism between quotient ideal-power Hom module
stages. -/
noncomputable def powerQuotientHomModuleStageMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerQuotientHomModuleStage M n ⟶ I.powerQuotientHomModuleStage N n :=
  ModuleCat.ofHom (I.powerQuotientHomMap f n)

/-- Applying a quotient module stage map postcomposes with the induced quotient map. -/
@[simp]
theorem powerQuotientHomModuleStageMap_apply (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (φ : I.powerQuotientHom M n) :
    (I.powerQuotientHomModuleStageMap f n).hom φ =
      (I.powerAnnihilatedQuotientMap f n).comp φ := sorry

/-- The quotient module-stage maps commute with ideal-power restriction transitions. -/
theorem powerQuotientHomModuleStageMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerQuotientHomModuleTransition M n ≫
        I.powerQuotientHomModuleStageMap f (n + 1) =
      I.powerQuotientHomModuleStageMap f n ≫
        I.powerQuotientHomModuleTransition N n := sorry

/-- The quotient module stage map induced by the identity is the identity. -/
@[simp]
theorem powerQuotientHomModuleStageMap_id (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    I.powerQuotientHomModuleStageMap (LinearMap.id : M →ₗ[R] M) n = 𝟙 _ := sorry

/-- Quotient module stage maps preserve composition. -/
theorem powerQuotientHomModuleStageMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    I.powerQuotientHomModuleStageMap (g.comp f) n =
      I.powerQuotientHomModuleStageMap f n ≫ I.powerQuotientHomModuleStageMap g n := sorry

/-- The successor naturality condition for the module-valued quotient ideal-power Hom diagrams. -/
theorem powerQuotientHomModuleDiagramMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerQuotientHomModuleDiagram M).map (homOfLE (Nat.le_succ n)) ≫
        I.powerQuotientHomModuleStageMap f (n + 1) =
      I.powerQuotientHomModuleStageMap f n ≫
        (I.powerQuotientHomModuleDiagram N).map (homOfLE (Nat.le_succ n)) := sorry

/-- The natural transformation between module-valued quotient ideal-power Hom diagrams induced
by postcomposition with a linear map. -/
noncomputable def powerQuotientHomModuleDiagramMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    I.powerQuotientHomModuleDiagram M ⟶ I.powerQuotientHomModuleDiagram N :=
  NatTrans.ofSequence
    (fun n ↦ I.powerQuotientHomModuleStageMap f n)
    (I.powerQuotientHomModuleDiagramMap_naturality f)

/-- The component of `powerQuotientHomModuleDiagramMap` at `n` is its quotient Hom stage map. -/
@[simp]
theorem powerQuotientHomModuleDiagramMap_app (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerQuotientHomModuleDiagramMap f).app n =
      I.powerQuotientHomModuleStageMap f n := sorry

/-- The module-valued quotient ideal-power Hom diagram map induced by the identity is the
identity. -/
@[simp]
theorem powerQuotientHomModuleDiagramMap_id (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    I.powerQuotientHomModuleDiagramMap (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := sorry

/-- Module-valued quotient ideal-power Hom diagram maps preserve composition. -/
theorem powerQuotientHomModuleDiagramMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    I.powerQuotientHomModuleDiagramMap (g.comp f) =
      I.powerQuotientHomModuleDiagramMap f ≫ I.powerQuotientHomModuleDiagramMap g := sorry

end QuotientHomSystem


end Ideal
