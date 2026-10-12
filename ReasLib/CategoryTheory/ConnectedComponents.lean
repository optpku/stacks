/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ConnectedComponents
import Mathlib.Tactic.CrossRefAttribute

/-!
# Connected-component quotient API

This file exposes the kernel and representative API for the quotient of a category by zigzag
connectedness. These statements belong to connected components themselves, independently of any
filteredness or bicategorical application.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ConnectedComponents

variable {J : Type u} [Category.{v} J]

/-- The canonical projection of a category to the discrete category of its connected
components. -/
@[stacks 04SC "connected-component quotient functor"]
def quotient (J : Type u) [Category.{v} J] :
    J ⥤ Discrete (ConnectedComponents J) :=
  functorToDiscrete _ id

/-- The connected-component quotient sends an object to its component class. -/
@[simp]
theorem quotient.obj (X : J) :
    (quotient J).obj X = Discrete.mk (mk X) := sorry

namespace mk

/-- Two objects represent the same connected component exactly when a zigzag joins them. -/
@[stacks 04SC "kernel of the connected-component quotient"]
theorem eq_iff_zigzag {X Y : J} :
    mk X = mk Y ↔ Zigzag X Y := sorry

/-- Zigzag-connected objects represent the same connected component. -/
theorem eq_of_zigzag {X Y : J} (h : Zigzag X Y) :
    mk X = mk Y := sorry

/-- The endpoints of a morphism represent the same connected component. -/
theorem eq_of_hom {X Y : J} (f : X ⟶ Y) :
    mk X = mk Y := sorry

/-- Every connected component is represented by an object. -/
theorem surjective :
    Function.Surjective (mk : J → ConnectedComponents J) := sorry

/-- To prove a property of a connected component, it suffices to prove it on represented
components. -/
@[elab_as_elim]
theorem induction
    {motive : ConnectedComponents J → Prop} (q : ConnectedComponents J)
    (h : ∀ X : J, motive (mk X)) :
    motive q := sorry

end mk

/-- The connected-component quotient sends a morphism to the unique discrete morphism induced
by equality of its endpoint classes. -/
@[simp]
theorem quotient.map {X Y : J} (f : X ⟶ Y) :
    (quotient J).map f = Discrete.eqToHom (mk.eq_of_hom f) := sorry

namespace liftFunctor

/-- A functor descended from connected components computes on a represented component by
applying the original functor to its representative. -/
@[simp]
theorem mk {X : Type*} (F : J ⥤ Discrete X) (j : J) :
    ConnectedComponents.liftFunctor J F (ConnectedComponents.mk j) =
      (F.obj j).as := sorry

end liftFunctor

end CategoryTheory.ConnectedComponents
