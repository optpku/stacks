/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans.Identity
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.Forget.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.IdentitySection.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsolutePseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong transformation constructions for groupoid-fibred inertia

The owner definitions for the forgetful and identity-section strong transformations.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

variable (C) in
/-- Forgetting the selected automorphism is a strong transformation from groupoid-fibred
inertia to the identity pseudofunctor. -/
@[stacks 042H "groupoid-fibred inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor C) :
        Pseudofunctor
          (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C))
      (Pseudofunctor.id
        (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.toId
    (BasedCategory.Inertia.strictPseudofunctor C)
    (map_mem C)
    (BasedCategory.Inertia.forget.strongTrans C)

variable (C) in
/-- The identity-automorphism section is a strong transformation from the identity
pseudofunctor to groupoid-fibred inertia. -/
@[stacks 04Z3 "groupoid-fibred inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id
        (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C))
      ((pseudofunctor C) :
        Pseudofunctor
          (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.fromId
    (BasedCategory.Inertia.strictPseudofunctor C)
    (map_mem C)
    (BasedCategory.Inertia.identitySection.strongTrans C)

end Inertia

end FiberedCategoryOver.Groupoids

end CategoryTheory
