/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars along a sequential DGA system

This leaf records the identity and composition comparisons for restricting a differential
graded module along transition maps of a sequential inverse system of DGAs.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace CochainDGAlgebra.InverseSystem

variable {R : Type u} [CommRing R]

/-- Restriction along the reflexive transition of a DGA system leaves a module unchanged. -/
theorem restrictModule_transitionMap_refl
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) :
    CochainDGAlgebra.Hom.restrictModule (A.transitionMap (le_refl i)) M = M := by
  have h : A.transitionMap (le_refl i) =
      CochainDGAlgebra.Hom.id (A.obj (op i)) := A.map_id (op i)
  rw [h]
  rfl

/-- Iterated restriction along two DGA transitions agrees with restriction along their
composite transition. -/
theorem restrictModule_transitionMap_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) :
    CochainDGAlgebra.Hom.restrictModule (A.transitionMap hjk)
        (CochainDGAlgebra.Hom.restrictModule (A.transitionMap hij) M) =
      CochainDGAlgebra.Hom.restrictModule
        (A.transitionMap (Nat.le_trans hij hjk)) M := by
  have h : A.transitionMap (Nat.le_trans hij hjk) =
      CochainDGAlgebra.Hom.comp (A.transitionMap hij) (A.transitionMap hjk) :=
    A.map_comp (homOfLE hjk).op (homOfLE hij).op
  rw [h]
  rfl

/-- The canonical module isomorphism comparing a reflexive DGA transition with identity
restriction. -/
@[stacks 0GZG "identity coherence for restriction along a DGA inverse system"]
def restrictModuleReflIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) :
    CochainDGAlgebra.Hom.restrictModule (A.transitionMap (le_refl i)) M ≅ M :=
  { hom :=
      { hom := fun _ ↦ LinearMap.id
        comm_d := fun _ _ ↦ rfl
        comm_smul := by
          intro p m x a
          change M.smul p m x (A.transitionMap (le_refl i) m a) = M.smul p m x a
          have h : A.transitionMap (le_refl i) =
              CochainDGAlgebra.Hom.id (A.obj (op i)) := A.map_id (op i)
          rw [h]
          rfl }
    inv :=
      { hom := fun _ ↦ LinearMap.id
        comm_d := fun _ _ ↦ rfl
        comm_smul := by
          intro p m x a
          change M.smul p m x a = M.smul p m x (A.transitionMap (le_refl i) m a)
          have h : A.transitionMap (le_refl i) =
              CochainDGAlgebra.Hom.id (A.obj (op i)) := A.map_id (op i)
          rw [h]
          rfl }
    hom_inv_id := rfl
    inv_hom_id := rfl }

namespace restrictModuleReflIso

/-- The forward reflexive-restriction comparison is the identity in every degree. -/
@[simp]
theorem hom_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleReflIso A i M).hom.hom n = LinearMap.id := rfl

/-- The inverse reflexive-restriction comparison is the identity in every degree. -/
@[simp]
theorem inv_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleReflIso A i M).inv.hom n = LinearMap.id := rfl

end restrictModuleReflIso

/-- The canonical module isomorphism comparing successive restriction along DGA transitions
with restriction along the composite transition. -/
@[stacks 0GZG "composition coherence for restriction along a DGA inverse system"]
def restrictModuleCompIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) :
    CochainDGAlgebra.Hom.restrictModule (A.transitionMap hjk)
        (CochainDGAlgebra.Hom.restrictModule (A.transitionMap hij) M) ≅
      CochainDGAlgebra.Hom.restrictModule
        (A.transitionMap (Nat.le_trans hij hjk)) M :=
  { hom :=
      { hom := fun _ ↦ LinearMap.id
        comm_d := fun _ _ ↦ rfl
        comm_smul := by
          intro p m x a
          change M.smul p m x (A.transitionMap hij m (A.transitionMap hjk m a)) =
            M.smul p m x (A.transitionMap (Nat.le_trans hij hjk) m a)
          have h : A.transitionMap (Nat.le_trans hij hjk) =
              CochainDGAlgebra.Hom.comp (A.transitionMap hij) (A.transitionMap hjk) :=
            A.map_comp (homOfLE hjk).op (homOfLE hij).op
          rw [h]
          rfl }
    inv :=
      { hom := fun _ ↦ LinearMap.id
        comm_d := fun _ _ ↦ rfl
        comm_smul := by
          intro p m x a
          change M.smul p m x (A.transitionMap (Nat.le_trans hij hjk) m a) =
            M.smul p m x (A.transitionMap hij m (A.transitionMap hjk m a))
          have h : A.transitionMap (Nat.le_trans hij hjk) =
              CochainDGAlgebra.Hom.comp (A.transitionMap hij) (A.transitionMap hjk) :=
            A.map_comp (homOfLE hjk).op (homOfLE hij).op
          rw [h]
          rfl }
    hom_inv_id := rfl
    inv_hom_id := rfl }

namespace restrictModuleCompIso

/-- The forward iterated-restriction comparison is the identity in every degree. -/
@[simp]
theorem hom_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleCompIso A hij hjk M).hom.hom n = LinearMap.id := rfl

/-- The inverse iterated-restriction comparison is the identity in every degree. -/
@[simp]
theorem inv_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleCompIso A hij hjk M).inv.hom n = LinearMap.id := rfl

end restrictModuleCompIso

end CochainDGAlgebra.InverseSystem
