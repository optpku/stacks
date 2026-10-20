/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Sets.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Construction

/-!
# Two-fibre products of categories fibred in sets as a pseudofunctor

This leaf specializes the neutral full-subbicategory construction to the strict
discrete-fibration object property. The required closure instance is owned by
`Fibered.Sets.PseudoPullback`; no equivalence-invariant setoid closure is used.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets.TwoFibreProduct

variable (C) in
/-- The canonical two-fibre-product pseudofunctor on bundled cospans of categories fibred in
sets. It is the neutral full-subbicategory construction specialized to strict discrete
fibrations. -/
@[stacks 0047 "bundled-cospan pseudofunctor on categories fibred in sets"]
noncomputable def pseudofunctor :
    Pseudofunctor
      (Bicategory.Cospan
        (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C))
      (FiberedCategoryOver.Sets.{u, v, max w (max u (max v vB)), max v vB} C) :=
  _root_.CategoryTheory.TwoFibreProduct.pseudofunctor
    (BasedCategory.isFiberedInSets C)

end FiberedCategoryOver.Sets.TwoFibreProduct

end CategoryTheory

/- The non-`Prop` data are owned by the neutral explicit pseudo-pullback pseudofunctor and its
generic full-subbicategory lift. The Sets specialization contributes no witness data. -/
