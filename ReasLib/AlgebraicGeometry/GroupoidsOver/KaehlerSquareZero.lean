/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.TrivialDeformation

/-!
# The Kähler square-zero section

The universal differential defines a section of the coefficient projection
from the trivial square-zero extension by the module of Kähler differentials.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor TrivSqZeroExt

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {A B : CommRingCat.{u}} (v : A ⟶ B)

/-- The ring map sending `b` to `(b, d b)` in the Kähler square-zero extension. -/
def trivSqZeroCan : B ⟶ trivSqZero B (CommRingCat.KaehlerDifferential v) :=
  CommRingCat.ofHom
    { toFun b := inl b + inr (CommRingCat.KaehlerDifferential.d b)
      map_one' := by
        have h : (CommRingCat.KaehlerDifferential.d (1 : B) :
            CommRingCat.KaehlerDifferential v) = 0 := by
          simpa using ModuleCat.Derivation.d_map (CommRingCat.KaehlerDifferential.D v) 1
        simp [h]
      map_mul' := by
        intro b c
        apply TrivSqZeroExt.ext <;>
          simp [ModuleCat.Derivation.d_mul]
      map_zero' := by
        have h : (CommRingCat.KaehlerDifferential.d (0 : B) :
            CommRingCat.KaehlerDifferential v) = 0 := by
          simpa using ModuleCat.Derivation.d_map (CommRingCat.KaehlerDifferential.D v) 0
        simp [h]
      map_add' := by
        intro b c
        apply TrivSqZeroExt.ext <;> simp [ModuleCat.Derivation.d_add] }

/-- The Kähler square-zero section has coordinates `(b, d b)`. -/
theorem trivSqZeroCan_apply (b : B) :
    (trivSqZeroCan v).hom b =
      inl b + inr (CommRingCat.KaehlerDifferential.d b) := rfl

/-- The Kähler square-zero section is a section of the coefficient projection. -/
theorem trivSqZeroCan_comp_fst :
    trivSqZeroCan v ≫ trivSqZeroHom B (CommRingCat.KaehlerDifferential v) = 𝟙 B := sorry

/-- The Kähler square-zero section and the first-summand inclusion agree on the base ring. -/
theorem trivSqZeroCan_comp_algebraMap :
    v ≫ trivSqZeroCan v = v ≫ trivSqZeroInl B (CommRingCat.KaehlerDifferential v) := sorry

variable {S : Scheme.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}

/-- The Kähler square-zero section respects the structure morphism induced from the base ring. -/
theorem trivSqZeroCan_spec (hv : Spec.map v ≫ σA = σB) :
    Spec.map (trivSqZeroCan v) ≫ σB =
      specTrivSqZero σB (CommRingCat.KaehlerDifferential v) := sorry

/-- The morphism over the base scheme induced by the Kähler square-zero section. -/
def specOverCan (hv : Spec.map v ≫ σA = σB) :
    Over.mk (specTrivSqZero σB (CommRingCat.KaehlerDifferential v)) ⟶ Over.mk σB :=
  specOverHom (trivSqZeroCan v) (trivSqZeroCan_spec v hv)

/-- The underlying scheme morphism of the Kähler square-zero section is its spectrum map. -/
theorem specOverCan_left (hv : Spec.map v ≫ σA = σB) :
    (specOverCan v hv).left = Spec.map (trivSqZeroCan v) := rfl

end AlgebraicGeometry.GroupoidsOver
