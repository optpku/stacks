/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.LiftTo.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.StrongTrans.LiftTo.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Construction

/-!
# Stable relative-inertia forgetful transformation

The relative-inertia forgetful maps assemble into a strong transformation after fixing the
universe of the source fibred categories to `max w vS`.  The construction is layered through the
full subbicategory of fibred objects, so the canonical pseudo-comma projection remains the public
endpoint rather than an equality-transported wrapper.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v vS w

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

namespace forget

/-- The ambient based forgetful transformation before restoring fibred-object and hom properties.
Its component is the canonical based relative-inertia forgetful functor. -/
private noncomputable def ambient (C : Type u) [Category.{v} C] :
    Pseudofunctor.StrongTrans
      (basedPseudofunctor C)
      (((Bicategory.PseudoComma.fst
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).comp
        (FiberedCategoryOver.toObject C).toPseudofunctor).comp
      (ObjectProperty.FullSubbicategory.ι
        (BasedCategory.isFibered.{u, v, max w vS, vS} C)).toPseudofunctor) where
  app S := BasedCategory.RelativeInertia.forget
    ((toBased C).obj S).hom
  naturality f := Iso.refl _
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

/-- The lifted full-subbicategory forgetful transformation has fibred source and target objects. -/
private noncomputable def full (C : Type u) [Category.{v} C] :
    Pseudofunctor.StrongTrans
      (objectLift C)
      ((Bicategory.PseudoComma.fst
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).comp
        (FiberedCategoryOver.toObject C).toPseudofunctor) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (basedPseudofunctor C)
    ((Bicategory.PseudoComma.fst
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).comp
      (FiberedCategoryOver.toObject C).toPseudofunctor)
    (objectLift.obj_mem)
    (ambient C)

/-- The final component of the forgetful lift preserves strongly cartesian arrows. -/
private theorem app_mem
    (C : Type u) [Category.{v} C]
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))) :
    FiberedCategoryOver.homProperty C
      ((objectLift C).obj S)
      (((Bicategory.PseudoComma.fst
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).comp
        (FiberedCategoryOver.toObject C).toPseudofunctor).obj S)
      ((full C).app S).hom := sorry

end forget

variable (C) in
/-- The stable relative-inertia forgetful maps form a strong transformation from the fibred
relative-inertia pseudofunctor to the canonical left pseudo-comma projection. -/
noncomputable def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor C) :
        Pseudofunctor
          (Bicategory.PseudoComma
            (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
            (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C)))
          (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Bicategory.PseudoComma.fst
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))) :=
  Bicategory.LocallyInducedBicategory.StrongTrans.liftTo
    (Q := FiberedCategoryOver.homProperty C)
    (objectLift C)
    (Bicategory.PseudoComma.fst
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C)))
    (objectLift.map_mem)
    (forget.full C)
    (forget.app_mem C)

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
