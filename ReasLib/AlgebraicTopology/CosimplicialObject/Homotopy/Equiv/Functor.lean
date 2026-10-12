/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Objectwise evaluation of cosimplicial homotopy equivalences

Functor-valued cosimplicial objects may be evaluated at an object of the source category.
This file records that evaluation preserves both structured product-free homotopy equivalences
and the corresponding morphism property.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v u' v'

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

namespace HomotopyEquiv

/-- Evaluating a cosimplicial homotopy equivalence between functor-valued cosimplicial objects at
an object gives a cosimplicial homotopy equivalence. -/
@[stacks 019Y "evaluation of a cosimplicial homotopy equivalence"]
def app {U V : CosimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V) (X : C) :
    HomotopyEquiv (U.flip.obj X) (V.flip.obj X) :=
  e.whiskerRight ((evaluation C D).obj X)

namespace app

/-- The forward map of an evaluated cosimplicial homotopy equivalence is the evaluated forward
map. -/
@[simp, stacks 019Y "evaluated homotopy-equivalence forward map"]
theorem hom {U V : CosimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V) (X : C) :
    (e.app X).hom = NatTrans.flipApp e.hom X := sorry

/-- The inverse map of an evaluated cosimplicial homotopy equivalence is the evaluated inverse
map. -/
@[simp, stacks 019Y "evaluated homotopy-equivalence inverse map"]
theorem inv {U V : CosimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V) (X : C) :
    (e.app X).inv = NatTrans.flipApp e.inv X := sorry

/-- A component of the forward map of an evaluated cosimplicial homotopy equivalence is evaluated
pointwise. -/
@[simp, stacks 019Y "evaluated homotopy-equivalence component"]
theorem hom_app {U V : CosimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V)
    (X : C) (Delta : SimplexCategory) :
    (e.app X).hom.app Delta = (e.hom.app Delta).app X := sorry

/-- A component of the inverse map of an evaluated cosimplicial homotopy equivalence is evaluated
pointwise. -/
@[simp, stacks 019Y "evaluated inverse homotopy-equivalence component"]
theorem inv_app {U V : CosimplicialObject (C ⥤ D)} (e : HomotopyEquiv U V)
    (X : C) (Delta : SimplexCategory) :
    (e.app X).inv.app Delta = (e.inv.app Delta).app X := sorry

end app

end HomotopyEquiv

namespace IsHomotopyEquivalence

/-- A homotopy-equivalence morphism between functor-valued cosimplicial objects remains a
homotopy equivalence after evaluation at an object. -/
@[stacks 019Y "evaluation preserves cosimplicial homotopy equivalences"]
theorem app {U V : CosimplicialObject (C ⥤ D)} {f : U ⟶ V}
    (hf : IsHomotopyEquivalence f) (X : C) :
    IsHomotopyEquivalence (NatTrans.flipApp f X) := sorry

end IsHomotopyEquivalence

end CategoryTheory.CosimplicialObject
