/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local hom action computations for the based-inertia pseudofunctor

This leaf exposes the action on each local hom category separately from object and `2`-cell
readouts.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

/-- The local action of the ordinary pseudofunctor is the inertia hom functor. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor local action"]
theorem pseudofunctor.mapFunctor
    (X Y : BasedCategory.{v₁, u₁} C) :
    (pseudofunctor C).mapFunctor X Y = Inertia.mapFunctor X Y := sorry

/-- The object action of the packaged local hom functor is the canonical inertia map. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor local object action"]
theorem pseudofunctor.mapFunctor.obj
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) :
    ((pseudofunctor C).mapFunctor X Y).obj F = Inertia.map F := sorry

/-- The morphism action of the packaged local hom functor is the canonical inertia `2`-morphism. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor local two-cell action"]
theorem pseudofunctor.mapFunctor.map
    {X Y : BasedCategory.{v₁, u₁} C} {F G : X ⥤ᵇ Y} (η : F ⟶ G) :
    ((pseudofunctor C).mapFunctor X Y).map η = Inertia.map₂ η := sorry

end Inertia

end BasedCategory
end CategoryTheory
