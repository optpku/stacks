/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Projections.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality computations for stack-valued two-fibre-product projections

The projection naturality isomorphisms are the ambient naturality cells lifted to the full
subbicategory of stacks. Both directions have direct forgetful readouts.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.TwoFibreProduct

/-- First-projection naturality is the ambient naturality isomorphism regarded at the stack
layer. -/
@[simp, stacks 026G "stack two-fibre-product first projection naturality"]
theorem pseudofunctor.fst.naturality
    {S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : S ⟶ T) :
    (pseudofunctor.fst J).naturality psi =
      Bicategory.InducedBicategory.isoMk
        ((pseudofunctor.fst.ambient J).naturality psi) := sorry

/-- Second-projection naturality is the ambient naturality isomorphism regarded at the stack
layer. -/
@[simp, stacks 026G "stack two-fibre-product second projection naturality"]
theorem pseudofunctor.snd.naturality
    {S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : S ⟶ T) :
    (pseudofunctor.snd J).naturality psi =
      Bicategory.InducedBicategory.isoMk
        ((pseudofunctor.snd.ambient J).naturality psi) := sorry

/-- Forgetting the forward first-projection naturality cell recovers the ambient forward
cell. -/
@[simp, stacks 026G "stack two-fibre-product first projection naturality forward readout"]
theorem pseudofunctor.fst.naturality.hom.toAmbient
    {S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : S ⟶ T) :
    HEq (((pseudofunctor.fst J).naturality psi).hom.hom)
      ((pseudofunctor.fst.ambient J).naturality psi).hom := sorry

/-- Forgetting the inverse first-projection naturality cell recovers the ambient inverse
cell. -/
@[simp, stacks 026G "stack two-fibre-product first projection naturality inverse readout"]
theorem pseudofunctor.fst.naturality.inv.toAmbient
    {S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : S ⟶ T) :
    HEq (((pseudofunctor.fst J).naturality psi).inv.hom)
      ((pseudofunctor.fst.ambient J).naturality psi).inv := sorry

/-- Forgetting the forward second-projection naturality cell recovers the ambient forward
cell. -/
@[simp, stacks 026G "stack two-fibre-product second projection naturality forward readout"]
theorem pseudofunctor.snd.naturality.hom.toAmbient
    {S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : S ⟶ T) :
    HEq (((pseudofunctor.snd J).naturality psi).hom.hom)
      ((pseudofunctor.snd.ambient J).naturality psi).hom := sorry

/-- Forgetting the inverse second-projection naturality cell recovers the ambient inverse
cell. -/
@[simp, stacks 026G "stack two-fibre-product second projection naturality inverse readout"]
theorem pseudofunctor.snd.naturality.inv.toAmbient
    {S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : S ⟶ T) :
    HEq (((pseudofunctor.snd J).naturality psi).inv.hom)
      ((pseudofunctor.snd.ambient J).naturality psi).inv := sorry

end StackOver.TwoFibreProduct

end CategoryTheory
