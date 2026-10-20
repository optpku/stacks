module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Module.IdealPower.Torsion

/-!
# Sequential Hom systems attached to powers of an ideal

This file is the algebraic, scheme-independent owner of the direct systems
`Hom_R(I^n, M)` and `Hom_R(I^n, M / M_n)`, where `M_n` is the submodule
annihilated by `I^n`.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace Ideal

section HomSystem

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `n`-th module in the ideal-power Hom system, `Hom_R(I^n, M)`. -/
abbrev powerHom (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :=
  (I ^ n : Ideal R) →ₗ[R] M

/-- The `n`-th ideal-power Hom module viewed as an additive commutative group. -/
noncomputable abbrev powerHomStage (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (I.powerHom M n)

/-- Restriction along `I^(n + 1) ≤ I^n` in the ideal-power Hom system. -/
noncomputable def powerHomTransition (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) : I.powerHomStage M n ⟶ I.powerHomStage M (n + 1) :=
  AddCommGrpCat.ofHom <|
    (LinearMap.lcomp R M (Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ))).toAddMonoidHom

/-- The ideal-power Hom transition is restriction to `I^(n + 1)`. -/
@[simp]
theorem powerHomTransition_apply (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (φ : I.powerHom M n) :
    (I.powerHomTransition M n).hom φ =
      φ.comp (Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ)) := sorry

/-- The sequential diagram `n ↦ Hom_R(I^n, M)`. -/
noncomputable def powerHomDiagram (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence (fun n ↦ I.powerHomTransition M n)

/-- Postcomposition by a linear map on the `n`-th ideal-power Hom module. -/
noncomputable def powerHomMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerHom M n →ₗ[R] I.powerHom N n :=
  LinearMap.compRight R f

/-- Postcomposition on the ideal-power Hom module sends `φ` to `f ∘ₗ φ`. -/
@[simp]
theorem powerHomMap_apply (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (φ : I.powerHom M n) :
    I.powerHomMap f n φ = f.comp φ := sorry

/-- The map of additive groups induced by postcomposition on the `n`-th ideal-power Hom module. -/
noncomputable def powerHomStageMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerHomStage M n ⟶ I.powerHomStage N n :=
  AddCommGrpCat.ofHom (I.powerHomMap f n).toAddMonoidHom

/-- The ideal-power Hom stage maps commute with the direct-system transitions. -/
theorem powerHomStageMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    I.powerHomTransition M n ≫ I.powerHomStageMap f (n + 1) =
      I.powerHomStageMap f n ≫ I.powerHomTransition N n := sorry

/-- The diagram-level successor naturality condition induced by a map of ideal-power Hom stages. -/
theorem powerHomDiagramMap_naturality (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerHomDiagram M).map (homOfLE (Nat.le_succ n)) ≫
        I.powerHomStageMap f (n + 1) =
      I.powerHomStageMap f n ≫
        (I.powerHomDiagram N).map (homOfLE (Nat.le_succ n)) := sorry

/-- The natural transformation between ideal-power Hom diagrams induced by postcomposition with
a linear map. -/
noncomputable def powerHomDiagramMap (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    I.powerHomDiagram M ⟶ I.powerHomDiagram N :=
  NatTrans.ofSequence
    (fun n ↦ I.powerHomStageMap f n)
    (I.powerHomDiagramMap_naturality f)

/-- The component of `powerHomDiagramMap` at `n` is the postcomposition stage map. -/
@[simp]
theorem powerHomDiagramMap_app (I : Ideal R) {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) :
    (I.powerHomDiagramMap f).app n = I.powerHomStageMap f n := sorry

/-- Postcomposition by the identity is the identity on an ideal-power Hom module. -/
@[simp]
theorem powerHomMap_id (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) :
    I.powerHomMap (LinearMap.id : M →ₗ[R] M) n = LinearMap.id := sorry

/-- Postcomposition on ideal-power Hom modules preserves composition. -/
theorem powerHomMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    I.powerHomMap (g.comp f) n = (I.powerHomMap g n).comp (I.powerHomMap f n) := sorry

/-- The stage map induced by the identity is the identity. -/
@[simp]
theorem powerHomStageMap_id (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) :
    I.powerHomStageMap (LinearMap.id : M →ₗ[R] M) n = 𝟙 _ := sorry

/-- The stage maps induced by linear maps preserve composition. -/
theorem powerHomStageMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (n : ℕ) :
    I.powerHomStageMap (g.comp f) n = I.powerHomStageMap f n ≫ I.powerHomStageMap g n := sorry

/-- The ideal-power Hom diagram map induced by the identity is the identity natural transformation. -/
@[simp]
theorem powerHomDiagramMap_id (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    I.powerHomDiagramMap (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := sorry

/-- The ideal-power Hom diagram maps induced by linear maps preserve composition. -/
theorem powerHomDiagramMap_comp (I : Ideal R) {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    I.powerHomDiagramMap (g.comp f) = I.powerHomDiagramMap f ≫ I.powerHomDiagramMap g := sorry

end HomSystem

section QuotientHomSystem

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `n`-th quotient Hom module `Hom_R(I^n, M / M_n)`. -/
abbrev powerQuotientHom (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :=
  (I ^ n : Ideal R) →ₗ[R] (M ⧸ I.powerAnnihilatedSubmodule M n)

/-- The `n`-th quotient Hom module viewed as an additive commutative group. -/
noncomputable abbrev powerQuotientHomStage (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (I.powerQuotientHom M n)

/-- Restriction of a map on `I^n` to the next ideal power `I^(n + 1)`. -/
noncomputable def powerQuotientHomRestriction (I : Ideal R) (n : ℕ) :
    (I ^ (n + 1) : Ideal R) →ₗ[R] (I ^ n : Ideal R) :=
  Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ)

/-- The quotient map from the `I^n`-annihilated quotient to the next stage. -/
noncomputable abbrev powerQuotientHomQuotientMap (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    M ⧸ I.powerAnnihilatedSubmodule M n →ₗ[R]
      M ⧸ I.powerAnnihilatedSubmodule M (n + 1) :=
  I.powerAnnihilatedSubmoduleQuotientMap M n.le_succ

/-- The transition map in the quotient ideal-power Hom system. -/
noncomputable def powerQuotientHomTransition (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    I.powerQuotientHomStage M n ⟶ I.powerQuotientHomStage M (n + 1) :=
  AddCommGrpCat.ofHom <|
    ((LinearMap.compRight R (I.powerQuotientHomQuotientMap M n)).comp
      (LinearMap.lcomp R _ (I.powerQuotientHomRestriction n))).toAddMonoidHom

/-- The quotient ideal-power Hom transition first restricts the source and then maps quotient
classes to the later quotient. -/
@[simp]
theorem powerQuotientHomTransition_apply (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) (φ : I.powerQuotientHom M n) :
    (I.powerQuotientHomTransition M n).hom φ =
      (I.powerQuotientHomQuotientMap M n).comp
        (φ.comp (I.powerQuotientHomRestriction n)) := sorry

/-- The sequential diagram `n ↦ Hom_R(I^n, M / M_n)`. -/
noncomputable def powerQuotientHomDiagram (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℕ ⥤ AddCommGrpCat :=
  Functor.ofSequence (fun n ↦ I.powerQuotientHomTransition M n)

end QuotientHomSystem

end Ideal
