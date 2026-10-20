/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteResidualHomology
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Continuous residual homology over the original left coefficient ring

Extend the actual finite-input compact residual chain by zero. Homological
degree i is placed at cochain degree -i. The quotient group acts before
forgetting it, and the displayed maps are then localized by the standard Q.
-/

@[expose] public section
open CategoryTheory
noncomputable section
-- Local instance justification (defeq pin): Residual homology uses the standard localized derived category and its canonical Q functor.
attribute [local instance] HasDerivedCategory.standard
universe u

namespace ResidualHomologyLeft

variable (Λ G Γ Q : Type u) [Ring Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)
variable (M : CategoryTheory.Action.ModuleCat.DiscreteModuleCat Λ Γ)
variable [Module.Finite Λ M.obj.V]

/-- Existing compact-derived chain after canonical double-op scalar restriction. -/
abbrev chain := FiniteResidualHomology.chain Λ G Γ Q φ ψ hexact hsurj M

/-- The original left-coefficient complex, with natural homological placement. -/
def cochain : CochainComplex (ModuleCat.{u} Λ) ℤ :=
  (chain Λ G Γ Q φ ψ hexact hsurj M).extend ComplexShape.embeddingDownNat

/-- The specified residual quotient action extended by zero. -/
def cochainAction (q : Q) : cochain Λ G Γ Q φ ψ hexact hsurj M ⟶
    cochain Λ G Γ Q φ ψ hexact hsurj M :=
  HomologicalComplex.extendMap
    (FiniteResidualHomology.frobenius Λ G Γ Q φ ψ hexact hsurj M q)
    ComplexShape.embeddingDownNat

/-- Canonical degree comparison; there is no geometric dimension shift. -/
def degreeIso (i : ℕ) : (cochain Λ G Γ Q φ ψ hexact hsurj M).X (-(i : ℤ)) ≅
    (chain Λ G Γ Q φ ψ hexact hsurj M).X i :=
  (chain Λ G Γ Q φ ψ hexact hsurj M).extendXIso ComplexShape.embeddingDownNat rfl

/-- The action in degree -i is the actual chain action under the degree comparison. -/
theorem cochainAction_f (q : Q) (i : ℕ) :
    (cochainAction Λ G Γ Q φ ψ hexact hsurj M q).f (-(i : ℤ)) =
      (degreeIso Λ G Γ Q φ ψ hexact hsurj M i).hom ≫
        (FiniteResidualHomology.frobenius Λ G Γ Q φ ψ hexact hsurj M q).f i ≫
        (degreeIso Λ G Γ Q φ ψ hexact hsurj M i).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

/-- Continuous homology in the standard derived category of left Λ-modules. -/
def derived : DerivedCategory (ModuleCat.{u} Λ) :=
  DerivedCategory.Q.obj (cochain Λ G Γ Q φ ψ hexact hsurj M)

/-- Localize the actual quotient-group endomorphism of the constructed complex. -/
def residualEnd (q : Q) : End (derived Λ G Γ Q φ ψ hexact hsurj M) :=
  DerivedCategory.Q.map (cochainAction Λ G Γ Q φ ψ hexact hsurj M q)

@[simp] theorem chainAction_one :
    FiniteResidualHomology.frobenius Λ G Γ Q φ ψ hexact hsurj M 1 = 𝟙 _ := by
  unfold FiniteResidualHomology.frobenius
  rw [NoncommResidualHomology.chainFrobenius_one]
  exact ((ModuleCat.restrictScalars (RingEquiv.opOp Λ).toRingHom).mapHomologicalComplex
    (ComplexShape.down ℕ)).map_id _

theorem chainAction_mul (q r : Q) :
    FiniteResidualHomology.frobenius Λ G Γ Q φ ψ hexact hsurj M (q * r) =
      FiniteResidualHomology.frobenius Λ G Γ Q φ ψ hexact hsurj M r ≫
        FiniteResidualHomology.frobenius Λ G Γ Q φ ψ hexact hsurj M q := by
  unfold FiniteResidualHomology.frobenius
  rw [NoncommResidualHomology.chainFrobenius_mul]
  exact ((ModuleCat.restrictScalars (RingEquiv.opOp Λ).toRingHom).mapHomologicalComplex
    (ComplexShape.down ℕ)).map_comp _ _

@[simp] theorem cochainAction_one :
    cochainAction Λ G Γ Q φ ψ hexact hsurj M 1 = 𝟙 _ := by
  unfold cochainAction
  rw [chainAction_one]
  exact HomologicalComplex.extendMap_id _ _

theorem cochainAction_mul (q r : Q) :
    cochainAction Λ G Γ Q φ ψ hexact hsurj M (q * r) =
      cochainAction Λ G Γ Q φ ψ hexact hsurj M r ≫
        cochainAction Λ G Γ Q φ ψ hexact hsurj M q := by
  unfold cochainAction
  rw [chainAction_mul]
  exact HomologicalComplex.extendMap_comp _ _ _

/-- The residual group acts by these very derived endomorphisms. -/
def residualAction : Q →* End (derived Λ G Γ Q φ ψ hexact hsurj M) where
  toFun := residualEnd Λ G Γ Q φ ψ hexact hsurj M
  map_one' := by
    unfold residualEnd
    rw [cochainAction_one]
    exact (DerivedCategory.Q (C := ModuleCat.{u} Λ)).map_id _
  map_mul' q r := by
    unfold residualEnd
    rw [cochainAction_mul]
    exact (DerivedCategory.Q (C := ModuleCat.{u} Λ)).map_comp _ _

theorem residualEnd_pow (q : Q) (n : ℕ) :
    residualEnd Λ G Γ Q φ ψ hexact hsurj M (q ^ n) =
      residualEnd Λ G Γ Q φ ψ hexact hsurj M q ^ n :=
  (residualAction Λ G Γ Q φ ψ hexact hsurj M).map_pow q n

end ResidualHomologyLeft
