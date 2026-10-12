/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison readouts for setoid-stack two-fibre products

This leaf records both directions of the identity and composition comparisons after forgetting
the thin-fibre condition, together with the pseudofunctor-level factorization through the ambient
groupoid-stack construction.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.TwoFibreProduct

/-- The forward identity comparison forgets to the forward comparison of the ambient
groupoid-stack pseudofunctor. -/
@[simp, stacks 0434 "setoid-stack identity forward comparison"]
theorem pseudofunctor.mapId.hom.toAmbient
    (S : Bicategory.Cospan
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor J).mapId S).hom.hom =
      ((ambientPseudofunctor J).mapId S).hom := sorry

/-- The inverse identity comparison forgets to the inverse comparison of the ambient
groupoid-stack pseudofunctor; heterogeneous equality accounts only for dependent endpoints. -/
@[stacks 0434 "setoid-stack identity inverse comparison"]
theorem pseudofunctor.mapId.inv.toAmbient
    (S : Bicategory.Cospan
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor J).mapId S).inv.hom ≍
      ((ambientPseudofunctor J).mapId S).inv := sorry

/-- The forward composition comparison forgets to the forward comparison of the ambient
groupoid-stack pseudofunctor; heterogeneous equality accounts only for dependent endpoints. -/
@[stacks 0434 "setoid-stack composition forward comparison"]
theorem pseudofunctor.mapComp.hom.toAmbient
    {R S T : Bicategory.Cospan
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor J).mapComp psi phi).hom.hom ≍
      ((ambientPseudofunctor J).mapComp psi phi).hom := sorry

/-- The inverse composition comparison forgets to the inverse ambient comparison;
heterogeneous equality accounts only for dependent endpoints. -/
@[stacks 0434 "setoid-stack composition inverse comparison"]
theorem pseudofunctor.mapComp.inv.toAmbient
    {R S T : Bicategory.Cospan
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)}
    (psi : R ⟶ S) (phi : S ⟶ T) :
    ((pseudofunctor J).mapComp psi phi).inv.hom ≍
      ((ambientPseudofunctor J).mapComp psi phi).inv := sorry

/-- Forgetting the thin-fibre condition after setoid-stack two-fibre products recovers the
ambient groupoid-stack pseudofunctor, including all action and comparison data. -/
@[stacks 0434 "setoid-stack forgetful factorization"]
theorem pseudofunctor.comp_forget :
    (pseudofunctor J).comp
        (StackOver.Setoids.forget J).toPseudofunctor =
      ambientPseudofunctor J := sorry

end StackOver.Setoids.TwoFibreProduct

end CategoryTheory
