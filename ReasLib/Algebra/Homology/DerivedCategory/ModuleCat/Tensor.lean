/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products of modules

@stack 064M

Module categories over commutative rings carry the canonical fixed-left,
fixed-right, and two-variable unbounded derived tensor functors.  This is the
plain-ring instance used by stalk and affine specializations of the generic
derived-tensor API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe w u

namespace ModuleCat

/-- The ordinary tensor product of modules admits canonical unbounded fixed-factor derived tensor
functors.  This is the module-level existence owner; comparison with a K-flat localization model
is supplied separately by an explicit resolution, rather than inferred from this proposition alone. -/
@[stacks 064M "module category"]
instance hasDerivedTensor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedCategory.DerivedTensor.Has (C := ModuleCat.{u} R) := sorry

/-- The tensor bifunctor on modules admits a canonical unbounded total left
derived bifunctor in both variables. -/
@[stacks 064M "module derived tensor bifunctor"]
instance hasDerivedTensorBifunctor (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedCategory.DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} R) := sorry

/-- The canonical two-variable derived tensor on modules remains a left-derived model after
fixing its right argument.  This is the comparison gate between the bifunctor and fixed-right
owners; it does not assert that the ambient homotopy localization is strong monoidal. -/
@[stacks 064M "module fixed-right derived tensor compatibility"]
instance derivedTensorBifunctorRightCompatible (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (E : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory.DerivedTensor.Bifunctor.Right.Compatible E := sorry

end ModuleCat

/- The ring-indexed notation is owned at the module instance boundary so downstream files that
  only need module-derived tensoring do not depend on the historical aggregation file.  Its body
  is the generic fixed-right object owner; `TensorProduct.lean` supplies the historical abbrev and
  bridge theorems separately. -/
namespace DerivedTensorProduct

set_option quotPrecheck false in
scoped notation:70 K:70 " ⊗[" R:70 "]^L " L:71 =>
  DerivedCategory.DerivedTensor.Right.obj (C := ModuleCat R) K L

end DerivedTensorProduct
