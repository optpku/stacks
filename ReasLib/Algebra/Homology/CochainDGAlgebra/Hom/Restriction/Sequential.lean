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
    CochainDGAlgebra.Hom.restrictModule (A.transitionMap (le_refl i)) M = M := sorry

/-- Iterated restriction along two DGA transitions agrees with restriction along their
composite transition. -/
theorem restrictModule_transitionMap_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) :
    CochainDGAlgebra.Hom.restrictModule (A.transitionMap hjk)
        (CochainDGAlgebra.Hom.restrictModule (A.transitionMap hij) M) =
      CochainDGAlgebra.Hom.restrictModule
        (A.transitionMap (Nat.le_trans hij hjk)) M := sorry

/-- The canonical module isomorphism comparing a reflexive DGA transition with identity
restriction. -/
@[stacks 0GZG "identity coherence for restriction along a DGA inverse system"]
def restrictModuleReflIso
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) :
    CochainDGAlgebra.Hom.restrictModule (A.transitionMap (le_refl i)) M ≅ M :=
  { hom :=
      { hom := fun _ ↦ LinearMap.id
        comm_d := sorry
        comm_smul := sorry }
    inv :=
      { hom := fun _ ↦ LinearMap.id
        comm_d := sorry
        comm_smul := sorry }
    hom_inv_id := sorry
    inv_hom_id := sorry }

namespace restrictModuleReflIso

/-- The forward reflexive-restriction comparison is the identity in every degree. -/
@[simp]
theorem hom_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleReflIso A i M).hom.hom n = LinearMap.id := sorry

/-- The inverse reflexive-restriction comparison is the identity in every degree. -/
@[simp]
theorem inv_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) (i : ℕ)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleReflIso A i M).inv.hom n = LinearMap.id := sorry

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
        comm_d := sorry
        comm_smul := sorry }
    inv :=
      { hom := fun _ ↦ LinearMap.id
        comm_d := sorry
        comm_smul := sorry }
    hom_inv_id := sorry
    inv_hom_id := sorry }

namespace restrictModuleCompIso

/-- The forward iterated-restriction comparison is the identity in every degree. -/
@[simp]
theorem hom_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleCompIso A hij hjk M).hom.hom n = LinearMap.id := sorry

/-- The inverse iterated-restriction comparison is the identity in every degree. -/
@[simp]
theorem inv_hom
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (M : DifferentialGradedModule.{u, v} (A.obj (op i))) (n : ℤ) :
    (restrictModuleCompIso A hij hjk M).inv.hom n = LinearMap.id := sorry

end restrictModuleCompIso

end CochainDGAlgebra.InverseSystem
