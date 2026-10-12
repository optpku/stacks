/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Representability
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Constant

/-!
# Constant-object restriction of simplicial mapping presheaves

This module owns the restriction of a simplicial mapping presheaf to constant test objects. It is
independent of dimension bounds and of any limit-based representability criterion.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type uC} [Category.{vC} C]

section Definition

variable (U : SSet.{uS}) (T : SimplicialObject C)
variable [HasConstCopowers U C]

/-- The restriction of the simplicial mapping presheaf from `U` to `T` along the constant-object
functor. Its value at `X` is the type of maps from the `U`-indexed copower of the constant
simplicial object on `X` to `T`. -/
@[stacks 017J "constant-object restriction"]
def constRestriction : Cᵒᵖ ⥤ Type vC :=
  (copower.constFunctor U).op ⋙ yoneda.obj T

/-- Evaluating the constant-object restriction at `X` gives the morphisms from the corresponding
constant copower to `T`. -/
@[simp, stacks 017J "constant-object restriction value"]
theorem constRestriction.obj (X : Cᵒᵖ) :
    (constRestriction U T).obj X =
      (copower U ((const C).obj X.unop) ⟶ T) := sorry

/-- The action of the constant-object restriction is precomposition by the copower of the
corresponding constant-object morphism. -/
@[simp, stacks 017J "constant-object restriction map"]
theorem constRestriction.map {X Y : C} (f : X ⟶ Y)
    (g : (constRestriction U T).obj (op Y)) :
    (constRestriction U T).map f.op g =
      copower.hom U ((const C).map f) ≫ g := sorry

end Definition

section Restriction

variable (U : SSet.{uS}) (T : SimplicialObject C)
variable [HasCopowers U C]

/-- With copowers by arbitrary simplicial objects available, the constant-object test
presheaf is the restriction of the global mapping presheaf along `SimplicialObject.const C`. -/
@[stacks 017J "constant-object restriction of the mapping presheaf"]
theorem constRestriction_eq :
    constRestriction U T = (const C).op ⋙ internalHom.presheaf U T := sorry

end Restriction

end CategoryTheory.SimplicialObject.internalHom
