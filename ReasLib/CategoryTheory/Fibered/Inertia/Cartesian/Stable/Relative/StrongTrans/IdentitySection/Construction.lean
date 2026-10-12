/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.LiftFrom.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor.StrongTrans.LiftFrom.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Construction
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Stable relative-inertia identity-section transformation

The relative identity sections are assembled in three explicit layers.  We first construct the
based naturality isomorphism, then lift its target through the full subbicategory of fibred
objects, and finally restore the hom property for strongly cartesian arrows.  This keeps the
canonical pseudo-comma projection as the public source endpoint.
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

namespace identitySection

private noncomputable def projection (C : Type u) [Category.{v} C] :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C)))
      ((BasedCategory.isFibered.{u, v, max w vS, vS} C).FullSubbicategory) :=
  (Bicategory.PseudoComma.fst
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).comp
    (FiberedCategoryOver.toObject C).toPseudofunctor

private noncomputable def projectionAmbient (C : Type u) [Category.{v} C] :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C)))
      (BasedCategory.{vS, max w vS} C) :=
  (projection C).comp
    (ObjectProperty.FullSubbicategory.ι
      (BasedCategory.isFibered.{u, v, max w vS, vS} C)).toPseudofunctor

private theorem component_comm
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))}
    (f : S ⟶ T)
    (x : ((projectionAmbient C).obj S).obj) :
    (((projectionAmbient C).map f ≫
        BasedCategory.RelativeInertia.identitySection
          ((toBased C).obj T).hom).obj x).aut.hom ≫ 𝟙 _ =
      (𝟙 _ ≫
        ((BasedCategory.RelativeInertia.identitySection
            ((toBased C).obj S).hom ≫
          (basedPseudofunctor C).map f).obj x).aut.hom) := sorry

private noncomputable def component
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))}
    (f : S ⟶ T) (x : ((projectionAmbient C).obj S).obj) :
    (((projectionAmbient C).map f ≫
        BasedCategory.RelativeInertia.identitySection
          ((toBased C).obj T).hom).obj x) ≅
      ((BasedCategory.RelativeInertia.identitySection
          ((toBased C).obj S).hom ≫ (basedPseudofunctor C).map f).obj x) :=
  CategoryTheory.RelativeInertia.isoMk
    ((toBased C).obj T).hom.toFunctor (Iso.refl _) (component_comm f x)

private noncomputable def component_naturality
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))}
    (f : S ⟶ T) :
    (projectionAmbient C).map f ≫
        BasedCategory.RelativeInertia.identitySection ((toBased C).obj T).hom ≅
      BasedCategory.RelativeInertia.identitySection ((toBased C).obj S).hom ≫
        (basedPseudofunctor C).map f :=
  BasedNatIso.ofComponents (component f)
    (fun _ ↦ sorry) (fun _ ↦ sorry)

private noncomputable def ambient (C : Type u) [Category.{v} C] :
    Pseudofunctor.StrongTrans
      (projectionAmbient C)
      (basedPseudofunctor C) where
  app S := BasedCategory.RelativeInertia.identitySection ((toBased C).obj S).hom
  naturality f := component_naturality f
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

private noncomputable def full (C : Type u) [Category.{v} C] :
    Pseudofunctor.StrongTrans (projection C) (objectLift C) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftFrom
    (projection C)
    (basedPseudofunctor C)
    (objectLift.obj_mem)
    (ambient C)

private theorem app_mem
    (C : Type u) [Category.{v} C]
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))) :
    FiberedCategoryOver.homProperty C
      ((Bicategory.PseudoComma.fst
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
          (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))).obj S)
      ((objectLift C).obj S)
      ((full C).app S).hom := sorry

end identitySection

variable (C) in
/-- The stable relative-inertia identity sections form a strong transformation from the canonical
left pseudo-comma projection to the fibred relative-inertia pseudofunctor. -/
noncomputable def identitySection.strongTrans :
    Pseudofunctor.StrongTrans
      (Bicategory.PseudoComma.fst
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
        (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C)))
      ((pseudofunctor C) :
        Pseudofunctor
          (Bicategory.PseudoComma
            (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
            (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C)))
          (FiberedCategoryOver.{u, v, max w vS, vS} C)) :=
  Bicategory.LocallyInducedBicategory.StrongTrans.liftFrom
    (Q := FiberedCategoryOver.homProperty C)
    (Bicategory.PseudoComma.fst
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C)))
    (objectLift C)
    (objectLift.map_mem)
    (identitySection.full C)
    (identitySection.app_mem C)

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
