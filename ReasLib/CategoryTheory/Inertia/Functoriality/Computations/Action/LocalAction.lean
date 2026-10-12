/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Pseudofunctor

/-!
# Local-action computations for the ordinary inertia pseudofunctor

This leaf owns the local hom functor and its object and morphism actions, independently of the
global object, `1`-cell, and naturality leaves.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v w

namespace CategoryTheory
namespace Inertia

/-- The local functor of the inertia pseudofunctor is the bundled inertia hom functor. -/
@[simp, stacks 04Z4 "inertia pseudofunctor local action"]
theorem pseudofunctor.mapFunctor (C D : Cat.{v, u}) :
    pseudofunctor.mapFunctor C D = catHomFunctor C D := sorry

/-- The local functor of the inertia pseudofunctor acts by the canonical inertia map. -/
@[simp, stacks 04Z4 "inertia pseudofunctor local object action"]
theorem pseudofunctor.mapFunctor.obj
    {C D : Cat.{v, u}} (F : C ⟶ D) :
    ((pseudofunctor).mapFunctor C D).obj F =
      (Inertia.map F.toFunctor).toCatHom := sorry

/-- The local functor of the inertia pseudofunctor acts on `2`-cells by the canonical induced
inertia transformation. -/
@[simp, stacks 04Z4 "inertia pseudofunctor local two-cell action"]
theorem pseudofunctor.mapFunctor.map
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    ((pseudofunctor).mapFunctor C D).map η =
      (Inertia.map₂ η.toNatTrans).toCatHom₂ := sorry

end Inertia
end CategoryTheory
