/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.TensorProduct.CommonField
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.CommonField.TensorMap
import StacksCheckRecall

@[expose] public section

/-!
# Tensor products of strict henselizations

@stack 0GIP

Lemma 10.156.6 is recalled through explicit composable layers.  A raw map
`B ⊗[A] C →+* K` with kernel `pD` first factors through `pD.ResidueField`.
The source-facing `CommonField.Model` then records supplied compatible
relative separable-closure realizations of the four chosen
strict-henselization residue fields in one common field `K`, inducing a
`ResidueSquare`.  Its reusable definition does not require `K` to be
separably algebraically closed; the source's separably algebraically closed
`κ` gives existence of such a model through `Model.exists_of_tensorMap`.
That theorem remains existential, so a raw tensor-product map never selects
maps between arbitrary strict henselizations as public data.  The four source
alternatives remain bundled in
`IsAdmissible`, with finite type retained where the source's quasi-finite
terminology requires it.
-/

/- Lemma 10.156.6, tag `0GIP`: the source begins with `D = B ⊗[A] C`, a map
`D →+* κ`, and the four primes given by its restrictions.  The kernel equality
gives the factor through `pD.ResidueField`.  Its proof next constructs the
four relative separable closures inside `κ` and uses them to construct the
strict henselizations and their comparison maps.  Here each such realization
is exposed through `LocalModel.ofLocalMap`, while
`Model.exists_of_tensorMap` supplies the proposition-level assembly into
`CommonField.Model`.  `Model.realizesTensorMap` ties that model back to the
original raw tensor map.
The model induces a propositionally unique residue square and comparison.
Under any source admissibility alternative, the comparison's tensor-product
map is bijective, hence `Comparison.tensorEquiv` gives the source
isomorphism.  The formal model records induced residue-field data rather than
a noncanonical choice of comparison map or inverse. -/
@[stacks 0GIP "raw tensor-map common-field compatibility"]
#check @Algebra.TensorProduct.RingHom.restrictLeft
#check @Algebra.TensorProduct.RingHom.restrictRight
#check @Algebra.TensorProduct.RingHom.restrictBase
#check @Localization.AtPrime.TensorProduct.ResidueField.tensorMap
#check @Localization.AtPrime.TensorProduct.ResidueField.restrictLeft_tensorMap
#check @Localization.AtPrime.TensorProduct.ResidueField.restrictRight_tensorMap
#check @Localization.AtPrime.TensorProduct.ResidueField.restrictBase_tensorMap
#check @Localization.AtPrime.TensorProduct.ResidueField.tensorMap_lift
#check @Localization.AtPrime.TensorProduct.ResidueField.tensorMap_lift_of_ker_eq
#check @Localization.AtPrime.TensorProduct.CommonField.Model.realizesTensorMap
#check @Localization.AtPrime.TensorProduct.CommonField.Model.realizesTensorMap_ker
#check @Localization.AtPrime.TensorProduct.CommonField.Model.realizesTensorMap_left_ker
#check @Localization.AtPrime.TensorProduct.CommonField.Model.realizesTensorMap_right_ker
#check @Localization.AtPrime.TensorProduct.CommonField.Model.realizesTensorMap_base_ker
@[stacks 0GIP "relative separable-closure realization"]
#check @RingHom.SeparableClosure.Realization
#check @RingHom.SeparableClosure.Realization.mapOfRangeLe
#check @RingHom.SeparableClosure.Realization.existsUniqueCompatible
#check @RingHom.SeparableClosure.Realization.exists_of_isSepClosure
#check @IsLocalRing.ResidueField.LocalModel.ofLocalMap
#check @IsStrictHenselizationOf.ResidueField.map_isSepClosure
#check @IsStrictHenselizationOf.ResidueField.existsModel
@[stacks 0GIP "common-field residue model"]
#check @Localization.AtPrime.TensorProduct.CommonField.Model
#check @Localization.AtPrime.TensorProduct.CommonField.Model.spec
#check @Localization.AtPrime.TensorProduct.CommonField.Model.induces
#check @Localization.AtPrime.TensorProduct.CommonField.Model.induces_iff
#check @Localization.AtPrime.TensorProduct.CommonField.Model.existsUniqueSquare
#check @IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.CommonField.Model.exists_of_tensorMap
#check @IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.CommonField.Model.existsUniqueComparison
@[stacks 0GIP "common-field strict-henselization tensor comparison"]
#check @IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.CommonField.Model.existsBijectiveComparison
#check @Localization.AtPrime.TensorProduct.Comparison
#check @Localization.AtPrime.TensorProduct.Comparison.residueSourceLeft
#check @Localization.AtPrime.TensorProduct.Comparison.residueSourceRight
#check @Localization.AtPrime.TensorProduct.Comparison.residueLeftTarget
#check @Localization.AtPrime.TensorProduct.Comparison.residueRightTarget
#check @Localization.AtPrime.TensorProduct.Comparison.sourceLeft
#check @Localization.AtPrime.TensorProduct.Comparison.sourceLeft_scalar
#check @Localization.AtPrime.TensorProduct.Comparison.sourceLeft_residue
#check @Localization.AtPrime.TensorProduct.Comparison.comm
#check @Localization.AtPrime.TensorProduct.Comparison.toRingHomSquare
#check @Algebra.TensorProduct.RingHom.Square
#check @Algebra.TensorProduct.RingHom.Square.diagonal
#check @Algebra.TensorProduct.RingHom.Square.tensor
#check @Algebra.TensorProduct.RingHom.Square.includeLeft
#check @Algebra.TensorProduct.RingHom.Square.includeRight
#check @Algebra.TensorProduct.RingHom.Square.tmul
#check @Algebra.TensorProduct.RingHom.Square.map
#check @Algebra.TensorProduct.RingHom.Square.map_tmul
#check @Algebra.TensorProduct.RingHom.Square.map_comp_includeLeft
#check @Algebra.TensorProduct.RingHom.Square.map_comp_includeRight
#check @IsStrictHenselizationOf.BaseChange.AtPrime.IsAdmissible
#check @Localization.AtPrime.TensorProduct.ResidueSquare
#check @Localization.AtPrime.TensorProduct.ResidueSquare.IsRealizedBy
#check @IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.ResidueSquare.existsUniqueComparison
#check @Localization.AtPrime.TensorProduct.Comparison.toResidueSquare
#check @Localization.AtPrime.TensorProduct.ResidueSquare.isRealizedBy_toResidueSquare
#check @Localization.AtPrime.TensorProduct.Comparison.tensorMap
#check @Localization.AtPrime.TensorProduct.Comparison.tensorEquiv
#check @IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.Comparison.residueSourceLeft_isPurelyInseparable
#check @IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.Comparison.tensorMap_bijective
@[stacks 0GIP "residue-square consequence"]
#check @IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.ResidueSquare.existsBijectiveComparison
