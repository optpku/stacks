module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Pseudofunctor

/-!
# `2`-cell computations for the ordinary inertia pseudofunctor

This leaf identifies the packaged `2`-cell action with the canonical induced inertia
transformation and exposes its component readouts.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace Inertia

/-- The `2`-cell action of the inertia pseudofunctor is the bundled induced inertia
transformation. -/
@[simp, stacks 04Z4 "inertia pseudofunctor two-cell action"]
theorem pseudofunctor.map₂ {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    pseudofunctor.map₂ η = (Inertia.map₂ η.toNatTrans).toCatHom₂ := sorry

/-- Forgetting the Cat wrapper from the `2`-cell action recovers the induced natural
transformation. -/
@[simp, stacks 04Z4 "inertia pseudofunctor two-cell underlying transformation"]
theorem pseudofunctor.map₂.toNatTrans
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    ((pseudofunctor).map₂ η).toNatTrans =
      Inertia.map₂ η.toNatTrans := sorry

/-- The component of the inertia `2`-cell action is the canonical intertwined component. -/
@[simp, stacks 04Z4 "inertia pseudofunctor two-cell component"]
theorem pseudofunctor.map₂.app
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) (X : Inertia C) :
    ((pseudofunctor).map₂ η).toNatTrans.app X =
      Inertia.map₂.component η.toNatTrans X := sorry

/-- The ambient arrow underlying a component of the inertia `2`-cell action is the original
natural-transformation component. -/
@[simp, stacks 04Z4 "inertia pseudofunctor two-cell underlying component"]
theorem pseudofunctor.map₂.app.underlying
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) (X : Inertia C) :
    Inertia.hom (((pseudofunctor).map₂ η).toNatTrans.app X) =
      η.toNatTrans.app X.obj := sorry

end Inertia
end CategoryTheory
