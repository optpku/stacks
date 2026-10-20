module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Generic stalks of invertible scheme modules

The stalk of an invertible module at the generic point of an integral scheme is a
one-dimensional vector space.  This module chooses its canonical coordinate generator and
records its spanning and nonvanishing properties.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}
  [_root_.AlgebraicGeometry.IsIntegral X]

private noncomputable def genericStalkTensorInverseIso
    (L : X.Modules) [Modules.Invertible L] :
    (RingedSpace.stalkModuleCat L (genericPoint X) ⊗
        RingedSpace.stalkModuleCat (isInvertibleObject.inverse L) (genericPoint X)) ≅
      ModuleCat.of X.functionField X.functionField :=
  (RingedSpace.Tensor.Stalk.comparisonIso L (isInvertibleObject.inverse L)
      (genericPoint X)).symm ≪≫
    (RingedSpace.stalkModuleFunctor (genericPoint X)).mapIso
      (isInvertibleObject.tensorInverseIso L ≪≫
        (SheafOfModules.RingedSite.unitIsoTensorUnit
          (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)).symm) ≪≫
    (RingedSpace.unitStalkLinearEquiv (X := X.toRingedSpace) (genericPoint X)).toModuleIso

/-- The generic stalk of an invertible module on an integral scheme has rank one. -/
theorem stalk_rank_eq_one
    (L : X.Modules) [Modules.Invertible L] :
    Module.rank X.functionField (RingedSpace.stalkModuleCat L (genericPoint X)) = 1 := by
  have hprod :
      Module.rank X.functionField
          (RingedSpace.stalkModuleCat L (genericPoint X) ⊗
            RingedSpace.stalkModuleCat (isInvertibleObject.inverse L) (genericPoint X) :
              ModuleCat X.functionField) = 1 := by
    simpa using (genericStalkTensorInverseIso L).toLinearEquiv.rank_eq
  change Module.rank X.functionField
      (TensorProduct X.functionField
        ↑(RingedSpace.stalkModuleCat L (genericPoint X))
        ↑(RingedSpace.stalkModuleCat (isInvertibleObject.inverse L) (genericPoint X))) = 1
    at hprod
  rw [rank_tensorProduct'] at hprod
  have hleft :
      Module.rank X.functionField (RingedSpace.stalkModuleCat L (genericPoint X)) ≠ 0 := by
    intro h
    simp [h] at hprod
  have hright :
      Module.rank X.functionField
          (RingedSpace.stalkModuleCat (isInvertibleObject.inverse L) (genericPoint X)) ≠ 0 := by
    intro h
    simp [h] at hprod
  exact ((mul_eq_one_iff_of_one_le
    (Cardinal.one_le_iff_ne_zero.mpr hleft)
    (Cardinal.one_le_iff_ne_zero.mpr hright)).mp hprod).1

/-- A chosen generator of the generic stalk of an invertible module on an integral scheme. -/
noncomputable def stalkGenerator
  (L : X.Modules) [Modules.Invertible L] :
    RingedSpace.stalkModuleCat L (genericPoint X) :=
  (finDimVectorspaceEquiv 1 (stalk_rank_eq_one L)).symm (fun _ ↦ 1)

/-- The chosen generic-stalk element spans the generic stalk. -/
theorem stalkGenerator_span
    (L : X.Modules) [Modules.Invertible L] :
    Submodule.span X.functionField {stalkGenerator L} = ⊤ := by
  let e := finDimVectorspaceEquiv 1 (stalk_rank_eq_one L)
  rw [Submodule.span_singleton_eq_top_iff]
  intro m
  refine ⟨e m 0, ?_⟩
  apply e.injective
  ext i
  fin_cases i
  simp [stalkGenerator, e]

/-- The chosen generator of the generic stalk is nonzero. -/
theorem stalkGenerator_ne_zero
    (L : X.Modules) [Modules.Invertible L] :
    stalkGenerator L ≠ 0 := by
  let e := finDimVectorspaceEquiv 1 (stalk_rank_eq_one L)
  intro h
  have h0 := congrArg (fun m ↦ e m 0) h
  simp [stalkGenerator, e] at h0

end AlgebraicGeometry.Scheme.Modules.Invertible
