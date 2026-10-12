/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv

/-!
# Functoriality of simplicial homotopy equivalences

Applying a covariant functor degreewise preserves both structured simplicial homotopy
equivalences and their associated morphism property.
-/

@[expose] public section

open CategoryTheory

universe u v u' v'

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {U V : SimplicialObject C}

namespace HomotopyEquiv

/-- Applying a covariant functor degreewise to a simplicial homotopy equivalence gives a
simplicial homotopy equivalence. -/
@[stacks 019Y "functoriality of simplicial homotopy equivalences"]
def whiskerRight (e : HomotopyEquiv U V) (F : C ⥤ D) :
    HomotopyEquiv (U ⋙ F) (V ⋙ F) :=
  e.map ((Functor.whiskeringRight SimplexCategoryᵒᵖ C D).obj F)

namespace whiskerRight

/-- The forward morphism of the functorial image is the degreewise image of the original
forward morphism. -/
@[simp, stacks 019Y "forward map of a functorial simplicial homotopy equivalence"]
theorem hom (e : HomotopyEquiv U V) (F : C ⥤ D) :
    (e.whiskerRight F).hom = Functor.whiskerRight e.hom F := sorry

/-- The inverse morphism of the functorial image is the degreewise image of the original inverse
morphism. -/
@[simp, stacks 019Y "inverse map of a functorial simplicial homotopy equivalence"]
theorem inv (e : HomotopyEquiv U V) (F : C ⥤ D) :
    (e.whiskerRight F).inv = Functor.whiskerRight e.inv F := sorry

end whiskerRight

/-- Evaluating a simplicial homotopy equivalence between functor-valued simplicial objects at an
object gives a simplicial homotopy equivalence. -/
@[stacks 019Y "objectwise evaluation of simplicial homotopy equivalences"]
def app {U V : SimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V) (X : C) :
    HomotopyEquiv (U.flip.obj X) (V.flip.obj X) :=
  e.whiskerRight ((evaluation C D).obj X)

namespace app

/-- The forward map of an evaluated homotopy equivalence is the evaluated forward map. -/
@[simp, stacks 019Y "forward map of an evaluated simplicial homotopy equivalence"]
theorem hom {U V : SimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V) (X : C) :
    (e.app X).hom = NatTrans.flipApp e.hom X := sorry

/-- The inverse map of an evaluated homotopy equivalence is the evaluated inverse map. -/
@[simp, stacks 019Y "inverse map of an evaluated simplicial homotopy equivalence"]
theorem inv {U V : SimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V) (X : C) :
    (e.app X).inv = NatTrans.flipApp e.inv X := sorry

/-- A component of the forward map of an evaluated homotopy equivalence is evaluated
pointwise. -/
@[simp, stacks 019Y "pointwise forward map of an evaluated homotopy equivalence"]
theorem hom_app {U V : SimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V)
    (X : C) (Δ : SimplexCategoryᵒᵖ) :
    (e.app X).hom.app Δ = (e.hom.app Δ).app X := sorry

/-- A component of the inverse map of an evaluated homotopy equivalence is evaluated
pointwise. -/
@[simp, stacks 019Y "pointwise inverse map of an evaluated homotopy equivalence"]
theorem inv_app {U V : SimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V)
    (X : C) (Δ : SimplexCategoryᵒᵖ) :
    (e.app X).inv.app Δ = (e.inv.app Δ).app X := sorry

end app

end HomotopyEquiv

namespace IsHomotopyEquivalence

/-- Applying a covariant functor degreewise preserves simplicial homotopy-equivalence
morphisms. -/
@[stacks 019Y "functors preserve simplicial homotopy equivalences"]
theorem whiskerRight {U V : SimplicialObject C} {f : U ⟶ V}
    (hf : IsHomotopyEquivalence f) (F : C ⥤ D) :
    IsHomotopyEquivalence (Functor.whiskerRight f F) := sorry

/-- A simplicial homotopy-equivalence morphism between functor-valued simplicial objects remains
a homotopy equivalence after evaluation at an object. -/
@[stacks 019Y "objectwise evaluation preserves simplicial homotopy equivalences"]
theorem app {U V : SimplicialObject (C ⥤ D)} {f : U ⟶ V}
    (hf : IsHomotopyEquivalence f) (X : C) :
    IsHomotopyEquivalence (NatTrans.flipApp f X) := sorry

end IsHomotopyEquivalence

end CategoryTheory.SimplicialObject
