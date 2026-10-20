/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison readouts for stack-valued two-fibre products

This leaf records stable identity and composition comparison readouts after forgetting the stack
condition, together with the pseudofunctor-level factorization through the ambient groupoid-fibred
construction.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.TwoFibreProduct

/-- The forward identity comparison forgets to the forward comparison of the ambient
two-fibre-product pseudofunctor. -/
@[simp, stacks 02ZL "ambient readout of the stack two-fibre-product identity comparison"]
theorem pseudofunctor.mapId.hom.toAmbient
    (S : Bicategory.Cospan
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor J).mapId S).hom.hom =
      ((ambientPseudofunctor J).mapId S).hom := sorry

/-- The inverse identity comparison forgets to the inverse comparison of the ambient
two-fibre-product pseudofunctor. -/
@[simp, stacks 02ZL "inverse ambient readout of the stack two-fibre-product identity comparison"]
theorem pseudofunctor.mapId.inv.toAmbient
    (S : Bicategory.Cospan
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor J).mapId S).inv.hom =
      ((ambientPseudofunctor J).mapId S).inv := sorry

/-- The forward composition comparison forgets to the forward comparison of the ambient
two-fibre-product pseudofunctor. -/
@[simp, stacks 02ZL "ambient readout of the stack two-fibre-product composition comparison"]
theorem pseudofunctor.mapComp.hom.toAmbient
    {R S T : Bicategory.Cospan
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor J).mapComp psi phi).hom.hom =
      ((ambientPseudofunctor J).mapComp psi phi).hom := sorry

/-- The inverse composition comparison forgets to the ambient inverse comparison;
heterogeneous equality accounts only for the dependent presentation of its endpoints. -/
@[stacks 02ZL "inverse ambient readout of the stack two-fibre-product composition comparison"]
theorem pseudofunctor.mapComp.inv.toAmbient
    {R S T : Bicategory.Cospan
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor J).mapComp psi phi).inv.hom ≍
      ((ambientPseudofunctor J).mapComp psi phi).inv := sorry

/-- The based natural transformation of the inverse composition comparison agrees with the
ambient based transformation up to dependent endpoint presentation. -/
@[stacks 02ZL "based-natural-transformation readout of stack composition comparison"]
theorem pseudofunctor.mapComp.inv.toBasedNatTrans
    {R S T : Bicategory.Cospan
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor J).mapComp psi phi).inv.hom.hom ≍
      ((ambientPseudofunctor J).mapComp psi phi).inv.hom := sorry

/-- The total natural transformation of the inverse composition comparison agrees with the
ambient total transformation up to dependent endpoint presentation. -/
@[stacks 02ZL "natural-transformation readout of stack composition comparison"]
theorem pseudofunctor.mapComp.inv.toNatTrans
    {R S T : Bicategory.Cospan
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor J).mapComp psi phi).inv.hom.hom.toNatTrans ≍
      ((ambientPseudofunctor J).mapComp psi phi).inv.hom.toNatTrans := sorry

/-- Forgetting the stack condition after stack-valued two-fibre products recovers the ambient
groupoid-fibred pseudofunctor, including its action and comparison data. -/
@[stacks 02ZL "forgetful comparison for the stack two-fibre-product pseudofunctor"]
theorem pseudofunctor.comp_forget :
    (pseudofunctor J).comp
        (StackOver.Groupoids.forget J).toPseudofunctor =
      ambientPseudofunctor J := sorry

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
