/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison readouts for stack-valued two-fibre products

This leaf records the identity and composition comparisons after forgetting the stack condition
and the pseudofunctor-level ambient factorization.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.TwoFibreProduct

/-- The forward identity comparison forgets to the forward comparison of the ambient
two-fibre-product pseudofunctor. -/
@[simp, stacks 026G "stack two-fibre-product identity forward comparison"]
theorem pseudofunctor.mapId.hom.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor J).mapId S).hom.hom =
      ((ambientPseudofunctor J).mapId S).hom := sorry

/-- The inverse identity comparison forgets to the inverse comparison of the ambient
two-fibre-product pseudofunctor. -/
@[simp, stacks 026G "stack two-fibre-product identity inverse comparison"]
theorem pseudofunctor.mapId.inv.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor J).mapId S).inv.hom =
      ((ambientPseudofunctor J).mapId S).inv := sorry

/-- The forward composition comparison forgets to the forward comparison of the ambient
two-fibre-product pseudofunctor. -/
@[simp, stacks 026G "stack two-fibre-product composition forward comparison"]
theorem pseudofunctor.mapComp.hom.toAmbient
    {R S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor J).mapComp psi phi).hom.hom =
      ((ambientPseudofunctor J).mapComp psi phi).hom := sorry

/-- The ambient inverse composition cell with endpoints expressed entirely at the ambient
pseudofunctor layer.  This owner isolates the endpoint transport introduced by stack bundling. -/
@[stacks 026G "stack two-fibre-product ambient composition inverse owner"]
noncomputable def pseudofunctor.mapComp.inv.ambient
    {R S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    (ambientPseudofunctor J).map psi ≫
        (ambientPseudofunctor J).map phi ⟶
      (ambientPseudofunctor J).map (psi ≫ phi) :=
  ((ambientPseudofunctor J).mapComp psi phi).inv

/-- The inverse composition comparison forgets to the named ambient inverse cell. -/
@[simp, stacks 026G "stack two-fibre-product composition inverse comparison"]
theorem pseudofunctor.mapComp.inv.toAmbient
    {R S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    HEq (((pseudofunctor J).mapComp psi phi).inv.hom)
      (pseudofunctor.mapComp.inv.ambient psi phi) := sorry

/-- Forgetting the stack condition after stack-valued two-fibre products recovers the ambient
fibred-category-valued pseudofunctor, including its `2`-cell and comparison data. -/
@[stacks 026G "stack two-fibre-product forgetful factorization"]
theorem pseudofunctor.comp_forget :
    (pseudofunctor J).comp (StackOver.forget J).toPseudofunctor =
      ambientPseudofunctor J := sorry

end StackOver.TwoFibreProduct

end CategoryTheory
