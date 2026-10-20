/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.StrictHenselization.BaseChange.AtPrime.TensorProduct
public import ReasLib.RingTheory.Henselian.StrictHenselization.ResidueField
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.CommonField
public import ReasLib.RingTheory.Localization.AtPrime.TensorProduct.CommonField.TensorMap

@[expose] public section

/-!
# Strict-henselization common-field realizations and comparisons

`Localization.AtPrime.TensorProduct.CommonField` owns the four-model
common-field package and its induced residue square.  This strict
henselization leaf adds the source-specific existence of such a model from a
tensor map to a separably closed field, followed by the lifting and
tensor-product-bijectivity conclusions needed for Stacks Lemma 10.156.6.
Its source-specific existence theorem is built over the generic
`IsStrictHenselizationOf.ResidueField.existsModel` API.

@stack 0GIP
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x y z t r

namespace IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.CommonField

section

variable {A : Type u} {B : Type v} {C : Type w} {K : Type r}
variable [CommRing A] [CommRing B] [CommRing C] [Field K]
variable [Algebra A B] [Algebra A C]
variable (pA : Ideal A) [pA.IsPrime]
variable (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
variable (pC : Ideal C) [pC.IsPrime]
variable (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB] [pD.LiesOver pC]
variable {Ash : Type x} {Bsh : Type y} {Csh : Type z} {Dsh : Type t}
variable [CommRing Ash] [CommRing Bsh] [CommRing Csh] [CommRing Dsh]
variable [Algebra (Localization.AtPrime pA) Ash]
variable [hAsh : IsStrictHenselizationOf (Localization.AtPrime pA) Ash]
variable [Algebra (Localization.AtPrime pB) Bsh]
variable [hBsh : IsStrictHenselizationOf (Localization.AtPrime pB) Bsh]
variable [Algebra (Localization.AtPrime pC) Csh]
variable [hCsh : IsStrictHenselizationOf (Localization.AtPrime pC) Csh]
variable [Algebra (Localization.AtPrime pD) Dsh]
variable [hDsh : IsStrictHenselizationOf (Localization.AtPrime pD) Dsh]

namespace Model

include hAsh hBsh hCsh hDsh in
/-- Tag 0GIP: a map from a tensor product to a separably closed field whose
kernel is the selected tensor prime admits compatible relative
separable-closure realizations for the four chosen strict henselizations.
The conclusion is existential so no noncanonical common-field model is made
public data. -/
@[stacks 0GIP "common-field model from a raw tensor map"]
theorem exists_of_tensorMap
    [IsSepClosed K]
    (map : B ⊗[A] C →+* K)
    (hker : RingHom.ker map = pD) :
    ∃ model : Localization.AtPrime.TensorProduct.CommonField.Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K),
      Localization.AtPrime.TensorProduct.CommonField.Model.realizesTensorMap
        pA pB pC pD model map := sorry

include hAsh hBsh hCsh hDsh in
/-- A common-field model determines a propositionally unique comparison of
the four chosen strict henselizations. -/
@[stacks 0GIP "strict-henselization comparison from a common-field model"]
theorem existsUniqueComparison
    (model : Localization.AtPrime.TensorProduct.CommonField.Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K)) :
    ∃! comparison : Localization.AtPrime.TensorProduct.Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh),
      Localization.AtPrime.TensorProduct.CommonField.Model.induces
        pA pB pC pD model (Localization.AtPrime.TensorProduct.Comparison.toResidueSquare
        (pA := pA) (pB := pB) (pC := pC) (pD := pD)
        (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) comparison) := sorry

include hAsh hBsh hCsh hDsh in
/-- Tag 0GIP: a common-field residue model produces a strict-henselization
comparison whose tensor-product map is bijective under any of the source
admissibility alternatives.  The source's separably closed field is used to
provide the model; the conclusion consumes only the supplied model. -/
@[stacks 0GIP "strict-henselization tensor comparison from a common field model"]
theorem existsBijectiveComparison
    (model : Localization.AtPrime.TensorProduct.CommonField.Model
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) (K := K))
    (hB : IsStrictHenselizationOf.BaseChange.AtPrime.IsAdmissible pA pB) :
    ∃ comparison : Localization.AtPrime.TensorProduct.Comparison
      (pA := pA) (pB := pB) (pC := pC) (pD := pD)
      (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh),
      Localization.AtPrime.TensorProduct.CommonField.Model.induces
        pA pB pC pD model (Localization.AtPrime.TensorProduct.Comparison.toResidueSquare
        (pA := pA) (pB := pB) (pC := pC) (pD := pD)
        (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) comparison) ∧
        Function.Bijective (Localization.AtPrime.TensorProduct.Comparison.tensorMap
          (pA := pA) (pB := pB) (pC := pC) (pD := pD)
          (Ash := Ash) (Bsh := Bsh) (Csh := Csh) (Dsh := Dsh) comparison) := sorry

end Model

end

end IsStrictHenselizationOf.BaseChange.AtPrime.TensorProduct.CommonField
