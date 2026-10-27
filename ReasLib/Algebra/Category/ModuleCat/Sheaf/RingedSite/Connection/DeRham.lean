/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.HomologicalComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Connection

/-! # De Rham complexes of integrable connections -/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace SheafOfModules.RingedSite.Connection

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {A O : Sheaf J CommRingCat.{max u v}} {φ : A ⟶ O}
variable {Ω F : ringedSiteModuleCategory J O}
variable {D : SheafOfModules.RelativeDerivation φ Ω}

/-- The coefficient module in degree zero, and module-valued normalized exterior
forms in positive degrees, regarded as modules over the coefficient sheaf. -/
def deRhamTerm (conn : Connection φ Ω D F) : ℕ → ringedSiteModuleCategory J A
  | 0 => (restrictionAlong φ).obj F
  | n + 1 => (restrictionAlong φ).obj (moduleTensor F (form O Ω (n + 1)))

/-- The connection in degree zero and its extension to module-valued forms in
positive degrees. -/
def deRhamDifferential (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D) :
    (n : ℕ) → deRhamTerm conn n ⟶ deRhamTerm conn (n + 1)
  | 0 => conn.hom
  | n + 1 => differential conn E (n + 1)

/-- Consecutive de Rham differentials of an integrable connection compose to zero. -/
theorem deRhamDifferential_comp (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (h : IsIntegrable conn E) (n : ℕ) :
    deRhamDifferential conn E n ≫ deRhamDifferential conn E (n + 1) = 0 := by
  cases n with
  | zero => exact h
  | succ n => exact squaresToZero_of_isIntegrable conn E h (n + 1)

/-- The nonnegative de Rham complex associated to an integrable connection,
with degree zero equal to its coefficient module. -/
def deRhamComplex (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D)
    (h : IsIntegrable conn E) : CochainComplex (ringedSiteModuleCategory J A) ℕ :=
  CochainComplex.of (deRhamTerm conn) (deRhamDifferential conn E)
    (deRhamDifferential_comp conn E h)

/-- The terms of the de Rham complex are the normalized module-valued forms. -/
theorem deRhamComplex_X (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D)
    (h : IsIntegrable conn E) (n : ℕ) :
    (deRhamComplex conn E h).X n = deRhamTerm conn n := rfl

/-- The degree-zero term of the de Rham complex is the coefficient module. -/
theorem deRhamComplex_X_zero (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (h : IsIntegrable conn E) :
    (deRhamComplex conn E h).X 0 = (restrictionAlong φ).obj F := rfl

/-- Positive-degree terms are tensors with the normalized exterior-form sheaves. -/
theorem deRhamComplex_X_succ (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (h : IsIntegrable conn E) (n : ℕ) :
    (deRhamComplex conn E h).X (n + 1) =
      (restrictionAlong φ).obj (moduleTensor F (form O Ω (n + 1))) := rfl

/-- The first differential of the de Rham complex is the given connection. -/
theorem deRhamComplex_d_zero (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (h : IsIntegrable conn E) :
    (deRhamComplex conn E h).d 0 1 = conn.hom := by
  change CochainComplex.of.d _ _ 0 (0 + 1) = _
  rw [CochainComplex.of_d]
  rfl

/-- Positive-degree differentials are the extended connection differentials. -/
theorem deRhamComplex_d_succ (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (h : IsIntegrable conn E) (n : ℕ) :
    (deRhamComplex conn E h).d (n + 1) (n + 1 + 1) =
      differential conn E (n + 1) := by
  change CochainComplex.of.d _ _ (n + 1) ((n + 1) + 1) = _
  rw [CochainComplex.of_d]
  rfl

end SheafOfModules.RingedSite.Connection
