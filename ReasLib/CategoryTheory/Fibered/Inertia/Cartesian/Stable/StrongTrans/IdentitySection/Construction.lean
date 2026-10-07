module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.StrongTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.StrongTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stable cartesian-inertia identity-section strong transformation

This leaf owns the strong transformation induced by the stable-universe identity section.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The identity-automorphism section is a strong transformation from the identity
pseudofunctor to the fibred-inertia pseudofunctor. -/
@[stacks 04Z3 "cartesian inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id
        (FiberedCategoryOver.{u, v, max w vS, vS} C))
      ((pseudofunctor C) :
        Pseudofunctor
          (FiberedCategoryOver.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.{u, v, max w vS, vS} C)) :=
  Bicategory.LocallyInducedBicategory.StrongTrans.fromId
    (objectLift.{u, v, vS, max w vS} C)
    objectLift.map_mem
    (objectLift.identitySection.strongTrans.{u, v, vS, w} C)
    (objectLift.identitySection.strongTrans.app_mem.{u, v, vS, w})

end FiberedCategoryOver.Inertia

end CategoryTheory
