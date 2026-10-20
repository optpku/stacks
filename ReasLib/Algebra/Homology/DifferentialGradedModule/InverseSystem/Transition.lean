/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Sequential
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transition maps of differential graded module systems

The structure of a DG-module inverse system stores only adjacent transition maps.  This leaf
canonically composes them to produce the map over every inequality of indices, together with
the identity, composition, and naturality API used by derived evaluation and pro-objects.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.System

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}

/-- The transition of a DG-module system from stage `j` to stage `i`, regarded as a map over
the DGA transition `A j ⟶ A i`. -/
@[stacks 0GZI "transition maps of a differential graded module inverse system"]
def mapLE (M : System.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :
    M.obj j ⟶ CochainDGAlgebra.Hom.restrictModule
      (A.transitionMap hij) (M.obj i) :=
  Nat.leRec
    (motive := fun j hij ↦ M.obj j ⟶ CochainDGAlgebra.Hom.restrictModule
      (A.transitionMap hij) (M.obj i))
    (CochainDGAlgebra.InverseSystem.restrictModuleReflIso A i (M.obj i)).inv
    (fun {j} hij f ↦
      M.map j ≫
        CochainDGAlgebra.Hom.restrictHom
          (A.stepMap j) f ≫
        (CochainDGAlgebra.InverseSystem.restrictModuleCompIso A hij
          (Nat.le_succ j) (M.obj i)).hom)
    hij

/-- The transition over a reflexive inequality is the inverse of the canonical identity
restriction comparison. -/
@[simp]
theorem mapLE_refl (M : System.{u, x, v} A) (i : ℕ) :
    M.mapLE (le_refl i) =
      (CochainDGAlgebra.InverseSystem.restrictModuleReflIso A i (M.obj i)).inv := sorry

/-- The transition over a successor inequality recovers the adjacent map stored by the
DG-module system. -/
@[simp]
theorem mapLE_succ (M : System.{u, x, v} A) (i : ℕ) :
    M.mapLE (Nat.le_succ i) = M.map i := sorry

/-- Arbitrary transition maps compose through an intermediate stage, with the canonical
comparison between iterated and composite restriction. -/
theorem mapLE_comp (M : System.{u, x, v} A) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    M.mapLE (Nat.le_trans hij hjk) =
      M.mapLE hjk ≫
        CochainDGAlgebra.Hom.restrictHom (A.transitionMap hjk) (M.mapLE hij) ≫
        (CochainDGAlgebra.InverseSystem.restrictModuleCompIso A hij hjk
          (M.obj i)).hom := sorry

/-- A morphism of DG-module systems commutes with every transition map, not only the adjacent
ones stored in the structure. -/
theorem Hom.naturalityLE {M N : System.{u, x, v} A} (f : M ⟶ N)
    {i j : ℕ} (hij : i ≤ j) :
    M.mapLE hij ≫ CochainDGAlgebra.Hom.restrictHom (A.transitionMap hij) (f.app i) =
      f.app j ≫ N.mapLE hij := sorry

end DifferentialGradedModule.InverseSystem.System
