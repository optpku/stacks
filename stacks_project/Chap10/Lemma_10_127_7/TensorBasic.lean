/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.Map

@[expose] public section

/-!
# Tensor-map support for Lemma 10.127.7

The reusable tensor-map statements used around Lemma 10.127.7 are owned by
Mathlib and `ReasLib.RingTheory.Algebra.TensorProduct.Map`.

@stack 05N8
-/

#check @Algebra.TensorProduct.ext
#check @Algebra.TensorProduct.map_comp
#check @Algebra.TensorProduct.map_comp_includeLeft
#check @Algebra.TensorProduct.map_comp_includeRight
#check @Algebra.TensorProduct.rTensor_comp_productMap_eq_id
#check @Algebra.TensorProduct.productMap_comp_rTensor_eq_id
#check @Algebra.TensorProduct.rTensorEquivOfInverse
#check @Algebra.TensorProduct.rTensor_surjective_of_generator_preimages
