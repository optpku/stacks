/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Normalization
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
import StacksCheckRecall

@[expose] public section

/-!
# Remark 15.115.1

The reusable owners for the reduced tensor-product normalization, its finite product factors, and
the DVR/Henselian consequences live in ReasLib.  This source-facing file is a tagged recall block;
it deliberately introduces no second chapter owner.

@stack 09EM
-/

open integralClosure.BaseChange DVR.BaseChange FieldExtension.TensorProduct

/- Remark 15.115.1: the comparison map and its pure-tensor formula. -/
@[stacks 09EM "Remark 15.115.1: tensor comparison map"]
#check @tensorMap
@[stacks 09EM "Remark 15.115.1: tensor comparison on pure tensors"]
#check @tensorMap_tmul
@[stacks 09EM "Remark 15.115.1 (2), integral comparison map"]
#check @tensorMap_isIntegral
@[stacks 09EM "Remark 15.115.1 (2), elementwise nilpotent comparison kernel"]
#check @tensorMap_kernel_isLocallyNilpotent

/- Remark 15.115.1: a finite reduced generic fiber is a nonempty finite product of finite field
extensions of `L`; the `AlgProduct` owner records the `L`-algebra structures explicitly. -/
@[stacks 09EM "Remark 15.115.1: finite algebra product decomposition"]
#check @AlgProduct.Decomposition.Finite
@[stacks 09EM "Remark 15.115.1: finite product of generic-fiber fields"]
#check @reduced_finiteProductOfFields
@[stacks 09EM "Remark 15.115.1: generic-fiber branch fields"]
#check @reduced_localization_isField
@[stacks 09EM "Remark 15.115.1: reduced generic fiber"]
#check @reduced_isReduced
@[stacks 09EM "Remark 15.115.1: finite-dimensional generic fiber"]
#check @reduced_finiteDimensional
@[stacks 09EM "Remark 15.115.1 (7), separable tensor product reduction equivalence"]
#check @tensorEquivReduced
@[stacks 09EM "Remark 15.115.1 (7), finite product of finite separable fields"]
#check @reduced_finiteProductOfSeparableFields

/- Remark 15.115.1 (1): the source normalization is Dedekind and the target normalization is a
finite product of Dedekind domains. -/
@[stacks 09EM "Remark 15.115.1 (1), source normalization is Dedekind"]
#check @sourceIsDedekindDomain
@[stacks 09EM "Remark 15.115.1 (1), target normalization is Dedekind"]
#check @targetIsDedekindRing
@[stacks 09EM "Remark 15.115.1 (1), target normalization Dedekind factors"]
#check @targetFiniteProductOfDedekindDomains

/- Remark 15.115.1 (3): maximal branches give extensions of discrete valuation rings. -/
@[stacks 09EM "Remark 15.115.1 (3), target localization DVR"]
#check @targetLocalizationIsDVR

/- Remark 15.115.1 (4): a Henselian source has a single DVR normalization branch. -/
@[stacks 09EM "Remark 15.115.1 (4), Henselian source normalization"]
#check @sourceIsDVR_of_henselian

/- Remark 15.115.1 (5): a Henselian target normalization is a finite product of DVRs.
The source's further inference `mᵢ = 1` fails when multiple tensor-product field factors lie
above the same source branch. -/
@[stacks 09EM "Remark 15.115.1 (5), Henselian target normalization DVR factors"]
#check @targetFiniteProductOfDVRs

/- Remark 15.115.1 (6): purely inseparable base change preserves both DVR normalizations. -/
@[stacks 09EM "Remark 15.115.1 (6), purely inseparable source normalization"]
#check @sourceIsDVR_of_finitePurelyInseparable
@[stacks 09EM "Remark 15.115.1 (6), purely inseparable target normalization"]
#check @targetIsDVR_of_finitePurelyInseparable

/- Remark 15.115.1 (7): finite separable base change is unreduced-free and gives finite
normalizations. -/
@[stacks 09EM "Remark 15.115.1 (7), finite separable source normalization"]
#check @sourceModuleFinite_of_finiteSeparable
@[stacks 09EM "Remark 15.115.1 (7), finite separable target normalization"]
#check @targetModuleFinite_of_finiteSeparable

/- Remark 15.115.1 (8): a Nagata source has finite normalization. -/
@[stacks 09EM "Remark 15.115.1 (8), Nagata source normalization"]
#check @sourceModuleFinite_of_nagata

/- Remark 15.115.1 (9): a Nagata target has finite normalization. -/
@[stacks 09EM "Remark 15.115.1 (9), Nagata target normalization"]
#check @targetModuleFinite_of_nagata

@[stacks 09EM "Remark 15.115.1 (3), maximal branch"]
#check @DVR.BaseChange.Branch
@[stacks 09EM "Remark 15.115.1 (3), localized DVR extension"]
#check @DVR.BaseChange.Branch.localExtension
@[stacks 09EM "Remark 15.115.1 (2), spectrum surjectivity"]
#check @spectrum_comap_surjective
