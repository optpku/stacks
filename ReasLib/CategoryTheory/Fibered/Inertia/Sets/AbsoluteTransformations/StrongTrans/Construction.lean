/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.Forget.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.IdentitySection.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsoluteTransformations.Maps.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong transformation constructions for set-fibred inertia

Owner definitions for the forgetful and identity-section strong transformations,
pointwise equivalence, and pseudofunctor equivalence.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory Pseudofunctor.StrongTrans

namespace FiberedCategoryOver.Sets.Inertia

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- Forgetting the selected automorphism is a strong transformation from set-fibred inertia to
the identity pseudofunctor. -/
@[stacks 042H "set-fibred inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor C) :
        Pseudofunctor
          (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C))
      (Pseudofunctor.id
        (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.toId
    (BasedCategory.Inertia.strictPseudofunctor C)
    (map_mem C)
    (BasedCategory.Inertia.forget.strongTrans C)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (C) in
/-- The canonical objectwise inertia equivalences, bundled as pointwise-equivalence data on the
forgetful strong transformation. -/
@[stacks 04Z3 "pointwise equivalence for set-fibred inertia"]
def forget.pointwiseEquivalence :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (forget.strongTrans C) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun X ↦ forget.equivalence X) (fun _ ↦ Iso.refl _)

variable (C) in
/-- Set-fibred inertia is equivalent to the identity pseudofunctor in every universe stable
under inertia. -/
@[stacks 04Z3 "set-fibred inertia pseudofunctor equivalence"]
def forget.pseudofunctorEquivalence :
    ((pseudofunctor C) :
        Pseudofunctor
          (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)) ≌
      Pseudofunctor.id
        (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C) :=
  (forget.pointwiseEquivalence C).toEquivalence

variable (C) in
/-- The identity-automorphism section is a strong transformation from the identity
pseudofunctor to set-fibred inertia. -/
@[stacks 04Z3 "set-fibred inertia identity-section strong transformation"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.id
        (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C))
      ((pseudofunctor C) :
        Pseudofunctor
          (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.Sets.{u, v, max w vS, vS} C)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.fromId
    (BasedCategory.Inertia.strictPseudofunctor C)
    (map_mem C)
    (BasedCategory.Inertia.identitySection.strongTrans C)

end FiberedCategoryOver.Sets.Inertia

end CategoryTheory
