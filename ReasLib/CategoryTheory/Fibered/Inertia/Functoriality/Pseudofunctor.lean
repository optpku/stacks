module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Whiskering
import Mathlib.Tactic.CrossRefAttribute

/-!
# The based-inertia pseudofunctor

This file owns the universe-changing strict pseudofunctor and its ordinary pseudofunctor view.
Projection-level formulas are deliberately layered in `Strict` and `Computations`.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂' u₃ v₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section InertiaPseudofunctor

open Bicategory
open scoped Bicategory

namespace Inertia

section PseudofunctorImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The strict-pseudofunctor pre-core for based inertia, assembled from the public local
functors and their whiskering API. -/
private def preCore :
    StrictPseudofunctorPreCore
      (BasedCategory.{v₁, u₁} C)
      (BasedCategory.{v₁, max u₁ v₁} C) where
  __ := PrelaxFunctor.mkOfHomFunctors inertia mapFunctor
  map_id := map.id
  map_comp := map.comp
  map₂_whisker_left := map₂.whiskerLeft
  map₂_whisker_right := map₂.whiskerRight

variable (C) in
/-- Absolute inertia is a universe-changing strict pseudofunctor on based categories over `C`.
The target object universe is `max u₁ v₁`, the universe of automorphism-equipped objects. -/
@[stacks 04Z4 "strict pseudofunctorial based inertia"]
def strictPseudofunctor :
    StrictPseudofunctor
      (BasedCategory.{v₁, u₁} C)
      (BasedCategory.{v₁, max u₁ v₁} C) :=
  StrictPseudofunctor.mk'' preCore

variable (C) in
/-- The ordinary pseudofunctor view of the strict based-inertia pseudofunctor. -/
@[stacks 04Z4 "pseudofunctorial based inertia"]
def pseudofunctor :
    Pseudofunctor
      (BasedCategory.{v₁, u₁} C)
      (BasedCategory.{v₁, max u₁ v₁} C) :=
  (strictPseudofunctor C).toPseudofunctor

end PseudofunctorImplementation

end Inertia
end InertiaPseudofunctor

end BasedCategory
end CategoryTheory
