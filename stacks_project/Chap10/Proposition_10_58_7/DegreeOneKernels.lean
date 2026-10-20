/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.Algebra.Module.Graded.HomogeneousMap.Component
public import ReasLib.Algebra.Module.Graded.HomogeneousMap.Translation
public import ReasLib.Algebra.Module.Graded.Decomposition.SMul
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.LinearAlgebra.Quotient.Map
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Torsion.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Degree-one kernel support

The former file contained a long proof for multiplication by one chosen degree-one element.  Its
reusable content belongs first at the generic homogeneous-map and quotient-map layers, so this file
is now a check-only surface.
-/

/- Proposition 10.58.7 (Tag 00K1): degree-one kernel and quotient infrastructure is recalled from
the shared homogeneous-map and stable power-kernel owners below. -/

/- API design: a future specialization should use `GradedModule.MapsTo.smul` with an injective
degree map, `componentMapOfEq` for arithmetic normalization of a selected component, the generic
`ker_isHomogeneous`/`range_isHomogeneous` bridges (only the kernel needs injectivity), the
power-level restrict-scalars companion, and the quotient-map injectivity criterion.  The conditional
quotient-injectivity APIs need no Noetherian hypothesis; only the separate stabilization theorem
`LinearMap.eventually_iSup_ker_pow_eq` asks for Noetherianity. -/

@[stacks 00K1 "degree-one kernel infrastructure"]
#check @GradedModule.MapsTo
#check @GradedModule.HomogeneousMap
#check @GradedModule.MapsTo.toLinearMap
#check @GradedModule.MapsTo.ext
#check @GradedModule.MapsTo.comp
#check @GradedModule.MapsTo.comp_id
#check @GradedModule.MapsTo.id_comp
#check @GradedModule.MapsTo.comp_assoc
#check @GradedModule.MapsTo.castDegree
#check @GradedModule.HomogeneousMap.comp
#check @GradedModule.HomogeneousMap.assocDegree
#check @GradedModule.HomogeneousMap.comp_assoc
#check @GradedModule.HomogeneousMap.id
#check @GradedModule.HomogeneousMap.compZero
#check @GradedModule.MapsTo.componentMap
#check @GradedModule.MapsTo.componentMap_coe
#check @GradedModule.MapsTo.componentMap_castDegree
#check @GradedModule.MapsTo.componentMap_comp
#check @GradedModule.MapsTo.componentMap_id
#check @GradedModule.MapsTo.componentMapOfEq
#check @GradedModule.MapsTo.smul
#check @GradedModule.MapsTo.pow
#check @GradedModule.MapsTo.ker_pow_isHomogeneous
#check @GradedModule.MapsTo.ker_pow_isHomogeneous_restrictScalars
#check @GradedModule.MapsTo.ker_pow_isHomogeneous_of_linearMap
#check @GradedModule.MapsTo.ker_pow_isHomogeneous_of_linearMap_restrictScalars
#check @GradedModule.MapsTo.smul_toLinearMap_eq_smul_id
@[stacks 00K1 "degree-one kernel and range infrastructure"]
#check @GradedModule.MapsTo.ker_isHomogeneous
#check @GradedModule.MapsTo.ker_isHomogeneous_restrictScalars
#check @GradedModule.MapsTo.range_isHomogeneous
#check @GradedModule.MapsTo.range_isHomogeneous_restrictScalars
#check @GradedModule.MapsTo.range_isHomogeneous_of_linearMap_restrictScalars
#check @GradedModule.MapsTo.ker_isHomogeneous_of_linearMap_restrictScalars
#check @DirectSum.coe_decompose_smul_of_left_mem
#check @DirectSum.coe_decompose_smul_vadd_of_left_mem
#check @DirectSum.coe_decompose_smul_of_right_mem
#check @DirectSum.coe_decompose_smul_vadd_of_right_mem
#check @AddAction.nat_vadd_int_point_injective
#check @AddAction.nat_vadd_int_scalar_injective
#check @DistribSMul.toLinearMap
#check @LinearMap.restrictScalars
#check @Submodule.torsionBy
#check @Submodule.mapQ_surjective_of_surjective
#check @Submodule.mapQ_injective_iff
#check @Submodule.mapQ_injective_of_comap_le
#check @LinearMap.eventually_iSup_ker_pow_eq
@[stacks 00K1 "stable power-kernel quotient infrastructure"]
#check @LinearMap.ker_pow_le_comap
#check @LinearMap.ker_pow_succ_eq_comap
#check @LinearMap.mapQ_ker_pow_injective_iff
#check @LinearMap.mapQ_ker_pow_injective_iff_eq
#check @LinearMap.mapQ_ker_pow_injective_of_iSup_eq
