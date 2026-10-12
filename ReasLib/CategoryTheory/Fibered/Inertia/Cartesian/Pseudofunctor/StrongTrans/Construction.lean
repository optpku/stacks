/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrongTrans.Lift
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition.Identity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.Forget.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans.IdentitySection.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object-level strong transformations for cartesian inertia

This file owns the based and fibred object-level transformations used before
the locally induced hom-property lift.  Their component, naturality, and
membership computations are in `...StrongTrans.Computations`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory.FiberedCategoryOver.Inertia.objectLift

open BasedCategory BasedFunctor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- Precomposing based-inertia forgetting by the canonical inclusion of fibred categories gives
a strong transformation to the underlying based-category pseudofunctor. -/
@[stacks 042H "based-level cartesian-inertia forgetful transformation"]
def forget.basedStrongTrans :
    Pseudofunctor.StrongTrans
      (((FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).comp
        (BasedCategory.Inertia.strictPseudofunctor.{u, v, max w vS, vS} C)).toPseudofunctor)
      (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).toPseudofunctor :=
  Pseudofunctor.StrongTrans.vcomp
    ((BasedCategory.Inertia.forget.strongTrans.{u, v, vS, w} C).precomp
      (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).toPseudofunctor)
    (Pseudofunctor.compId.strongTrans
      (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).toPseudofunctor)

variable (C) in
/-- Precomposing the based-inertia identity section by the canonical inclusion of fibred
categories gives a strong transformation from the underlying based-category pseudofunctor. -/
@[stacks 04Z3 "based-level cartesian-inertia identity-section transformation"]
def identitySection.basedStrongTrans :
    Pseudofunctor.StrongTrans
      (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).toPseudofunctor
      (((FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).comp
        (BasedCategory.Inertia.strictPseudofunctor.{u, v, max w vS, vS} C)).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    (Pseudofunctor.compId.pointwiseEquivalence
      (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).toPseudofunctor).inverse
    ((BasedCategory.Inertia.identitySection.strongTrans.{u, v, vS, w} C).precomp
      (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).toPseudofunctor)

variable (C) in
/-- Based-inertia forgetting lifted through the object property selecting fibred categories. -/
@[stacks 042H "fibred-object lift of cartesian-inertia forgetting"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      (FiberedCategoryOver.Inertia.objectLift.{u, v, vS, max w vS}
        C).toPseudofunctor
      (FiberedCategoryOver.toObject.{u, v, max w vS, vS} C).toPseudofunctor :=
  ObjectProperty.FullSubbicategory.StrongTrans.lift
    ((FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).comp
      (BasedCategory.Inertia.strictPseudofunctor.{u, v, max w vS, vS} C))
    (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C)
    (FiberedCategoryOver.Inertia.objectLift.obj_mem.{u, v, vS, max w vS} (C := C))
    (fun X ↦ X.property)
    (forget.basedStrongTrans.{u, v, vS, w} C)

variable (C) in
/-- The based-inertia identity section lifted through the object property selecting fibred
categories. -/
@[stacks 04Z3 "fibred-object lift of cartesian-inertia identity section"]
def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (FiberedCategoryOver.toObject.{u, v, max w vS, vS} C).toPseudofunctor
      (FiberedCategoryOver.Inertia.objectLift.{u, v, vS, max w vS}
        C).toPseudofunctor :=
  ObjectProperty.FullSubbicategory.StrongTrans.lift
    (FiberedCategoryOver.toBased.{u, v, max w vS, vS} C)
    ((FiberedCategoryOver.toBased.{u, v, max w vS, vS} C).comp
      (BasedCategory.Inertia.strictPseudofunctor.{u, v, max w vS, vS} C))
    (fun X ↦ X.property)
    (FiberedCategoryOver.Inertia.objectLift.obj_mem.{u, v, vS, max w vS} (C := C))
    (identitySection.basedStrongTrans.{u, v, vS, w} C)

/-- Every component of the object-lifted forgetful transformation preserves strongly
cartesian arrows. This is the property witness consumed by the locally induced lift. -/
theorem forget.strongTrans.app_mem
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.homProperty.{u, v, max w vS, vS} C
      ((FiberedCategoryOver.Inertia.objectLift.{u, v, vS, max w vS}
        C).obj X) X
      ((forget.strongTrans.{u, v, vS, w} C).app X).hom := sorry

/-- Every component of the object-lifted identity-section transformation preserves strongly
cartesian arrows. This is the property witness consumed by the locally induced lift. -/
theorem identitySection.strongTrans.app_mem
    (X : FiberedCategoryOver.{u, v, max w vS, vS} C) :
    FiberedCategoryOver.homProperty.{u, v, max w vS, vS} C X
      ((FiberedCategoryOver.Inertia.objectLift.{u, v, vS, max w vS}
        C).obj X)
      ((identitySection.strongTrans.{u, v, vS, w} C).app X).hom := sorry

end CategoryTheory.FiberedCategoryOver.Inertia.objectLift
