/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct.Sequential
import StacksCheckRecall

/-!
# Lemma 15.88.12

@stack 091L
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A]

/- Lemma 15.88.12 (Stacks 091L): a stagewise pro-isomorphism of derived inverse systems of
`A`-modules remains an isomorphism after tensoring by a fixed derived `A`-module and taking the
total right derived inverse limit. This is the `ModuleCat A` specialization of the generic
fixed-left tensor-derived-limit isomorphism theorem. -/
@[stacks 091L] #check
  DerivedLimit.tensorLeft_map_isIso (A := ModuleCat A)

end CategoryTheory.ModuleCat
