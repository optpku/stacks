/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.LocalAction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Local hom computations for relative inertia

This leaf exposes the object and morphism actions of the pseudo-comma relative-inertia hom
functor, together with mapped isomorphism projections.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

namespace mapFunctor

/-- The object action of the pseudo-comma relative-inertia hom functor is the square-induced
map. -/
@[simp, stacks 04Z4 "relative-inertia local hom object computation"]
theorem obj (f : S ⟶ T) :
    (mapFunctor S T).obj f = map f := sorry

/-- The morphism action of the pseudo-comma relative-inertia hom functor is the induced
relative-inertia `2`-morphism. -/
@[simp, stacks 04Z4 "relative-inertia local hom morphism computation"]
theorem map {f g : S ⟶ T} (η : f ⟶ g) :
    (mapFunctor S T).map η = map₂ η := sorry

end mapFunctor

namespace mapIso

/-- The forward `2`-morphism of the induced relative-inertia isomorphism is the action on the
forward pseudo-comma cell. -/
@[simp, stacks 04Z4 "relative-inertia local hom isomorphism forward computation"]
theorem hom {f g : S ⟶ T} (e : f ≅ g) :
    (mapIso e).hom = map₂ e.hom := sorry

/-- The inverse `2`-morphism of the induced relative-inertia isomorphism is the action on the
inverse pseudo-comma cell. -/
@[simp, stacks 04Z4 "relative-inertia local hom isomorphism inverse computation"]
theorem inv {f g : S ⟶ T} (e : f ≅ g) :
    (mapIso e).inv = map₂ e.inv := sorry

/-- The forward component of an induced pseudo-comma relative-inertia isomorphism is the
explicit component of the forward cell. -/
@[simp, stacks 04Z4 "relative-inertia local hom isomorphism forward component"]
theorem hom.app {f g : S ⟶ T} (e : f ≅ g)
    (A : (relativeInertia S.hom).obj) :
    (mapIso e).hom.toNatTrans.app A = map₂.component e.hom A := sorry

/-- The inverse component of an induced pseudo-comma relative-inertia isomorphism is the
explicit component of the inverse cell. -/
@[simp, stacks 04Z4 "relative-inertia local hom isomorphism inverse component"]
theorem inv.app {f g : S ⟶ T} (e : f ≅ g)
    (A : (relativeInertia S.hom).obj) :
    (mapIso e).inv.toNatTrans.app A = map₂.component e.inv A := sorry

/-- The arrow underlying a forward induced-isomorphism component is the left endpoint component
of the original pseudo-comma isomorphism. -/
@[simp, stacks 04Z4 "relative-inertia local hom forward underlying arrow"]
theorem hom.app.underlying {f g : S ⟶ T} (e : f ≅ g)
    (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom ((mapIso e).hom.toNatTrans.app A) =
      (Bicategory.PseudoComma.left₂ e.hom).toNatTrans.app A.obj := sorry

/-- The arrow underlying an inverse induced-isomorphism component is the left endpoint component
of the inverse pseudo-comma isomorphism. -/
@[simp, stacks 04Z4 "relative-inertia local hom inverse underlying arrow"]
theorem inv.app.underlying {f g : S ⟶ T} (e : f ≅ g)
    (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom ((mapIso e).inv.toNatTrans.app A) =
      (Bicategory.PseudoComma.left₂ e.inv).toNatTrans.app A.obj := sorry

end mapIso

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
