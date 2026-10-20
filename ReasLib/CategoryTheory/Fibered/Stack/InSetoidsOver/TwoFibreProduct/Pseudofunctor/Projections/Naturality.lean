/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Projections.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality computations for setoid-stack two-fibre-product projections

The projection naturality isomorphisms are the ambient comparisons lifted to the full
subbicategory of setoid stacks. Both directions have direct ambient readouts.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- First-projection naturality is the ambient naturality isomorphism regarded at the
setoid-stack layer. -/
@[simp, stacks 0434 "setoid-stack first projection naturality"]
theorem pseudofunctor.fst.naturality (psi : S ⟶ T) :
    (pseudofunctor.fst J).naturality psi =
      Bicategory.InducedBicategory.isoMk
        ((pseudofunctor.fst.ambient J).naturality psi) := sorry

/-- Forgetting the forward first-projection naturality cell recovers the ambient forward cell. -/
@[simp, stacks 0434 "setoid-stack first projection naturality forward readout"]
theorem pseudofunctor.fst.naturality.hom.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.fst J).naturality psi).hom.hom)
      ((pseudofunctor.fst.ambient J).naturality psi).hom := sorry

/-- Forgetting the inverse first-projection naturality cell recovers the ambient inverse cell. -/
@[simp, stacks 0434 "setoid-stack first projection naturality inverse readout"]
theorem pseudofunctor.fst.naturality.inv.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.fst J).naturality psi).inv.hom)
      ((pseudofunctor.fst.ambient J).naturality psi).inv := sorry

/-- Second-projection naturality is the ambient naturality isomorphism regarded at the
setoid-stack layer. -/
@[simp, stacks 0434 "setoid-stack second projection naturality"]
theorem pseudofunctor.snd.naturality (psi : S ⟶ T) :
    (pseudofunctor.snd J).naturality psi =
      Bicategory.InducedBicategory.isoMk
        ((pseudofunctor.snd.ambient J).naturality psi) := sorry

/-- Forgetting the forward second-projection naturality cell recovers the ambient forward cell. -/
@[simp, stacks 0434 "setoid-stack second projection naturality forward readout"]
theorem pseudofunctor.snd.naturality.hom.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.snd J).naturality psi).hom.hom)
      ((pseudofunctor.snd.ambient J).naturality psi).hom := sorry

/-- Forgetting the inverse second-projection naturality cell recovers the ambient inverse cell. -/
@[simp, stacks 0434 "setoid-stack second projection naturality inverse readout"]
theorem pseudofunctor.snd.naturality.inv.toAmbient (psi : S ⟶ T) :
    HEq (((pseudofunctor.snd J).naturality psi).inv.hom)
      ((pseudofunctor.snd.ambient J).naturality psi).inv := sorry

end StackOver.Setoids.TwoFibreProduct

end CategoryTheory
