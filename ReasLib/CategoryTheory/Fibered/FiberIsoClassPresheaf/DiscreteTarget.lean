/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Discrete
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fiber classes mapped into discrete fibrations

This leaf owns the canonical map from the fiberwise isomorphism classes of a fibred category to
the fiber objects of a discrete fibration. The construction only needs a based functor into the
discrete target; equivalence data belongs in the separate isomorphism layer.
-/

@[expose] public section

universe w u v uS uX uY uZ vX vY vZ

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

section SameObjectUniverse

variable {X : BasedCategory.{vX, uS} C}
variable {Y : BasedCategory.{vY, uS} C}
variable {Z : BasedCategory.{vZ, uS} C}

/-- A based functor from a fibred category into a discrete fibration sends each fiberwise
isomorphism class to the corresponding target fiber object. No equivalence hypothesis is needed. -/
@[stacks 02Y2 "based action from fiber classes to discrete fibers",
  stacks 04SI "based action from fiber classes to discrete fibers"]
noncomputable def fiberClassesMap
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    Functor.fiberIsoClassPresheaf X.p ⟶ Y.p.fiberObjectPresheaf :=
  BasedFunctor.fiberIsoClassMap F ≫
    (Functor.IsDiscreteFibration.fiberClassesIso Y.p).hom

/- Data audit: the map is the composite of the explicit quotient action of the fiber functors and
the canonical comparison from classes in a discrete fiber to its objects. It adds no choice. -/

namespace fiberClassesMap

/-- The component of `fiberClassesMap` is the canonical map from isomorphism classes through the
induced fiber functor into the discrete target fiber. -/
@[simp]
theorem app
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Y.p.IsDiscreteFibration] (U : Cᵒᵖ) :
    (BasedFunctor.fiberClassesMap F).app U =
      TypeCat.ofHom (F.fiberFunctor (unop U)).isoClassesToObj := by
  apply ConcreteCategory.ext_apply
  intro q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- On a represented source class, `fiberClassesMap` applies the induced fiber functor. -/
@[simp]
theorem app_mk
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (BasedFunctor.fiberClassesMap F).app U (Quotient.mk'' x) =
      (F.fiberFunctor (unop U)).obj x := by
  rfl

/-- For a discrete fibration, the map induced by the identity based functor is its canonical
comparison from fiber classes to fiber objects. -/
@[simp]
theorem id
    (X : BasedCategory.{vX, uS} C) [X.p.IsDiscreteFibration] :
    BasedFunctor.fiberClassesMap (𝟙 X : X ⥤ᵇ X) =
      (Functor.IsDiscreteFibration.fiberClassesIso X.p).hom := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.ext_apply
  intro q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- Mapping fiber classes through a composite into discrete fibrations is the class-to-object map
of the first functor followed by the object map of the second. -/
@[simp]
theorem comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) [X.p.IsFibered]
    [Y.p.IsDiscreteFibration] [Z.p.IsDiscreteFibration] :
    BasedFunctor.fiberClassesMap (F ⋙ G) =
      BasedFunctor.fiberClassesMap F ≫ BasedFunctor.fiberObjectMap G := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.ext_apply
  intro q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- A based natural transformation into a discrete fibration identifies the induced maps from
fiberwise isomorphism classes to target fiber objects. -/
theorem eq_of_hom
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Y.p.IsDiscreteFibration] (η : F ⟶ G) :
    BasedFunctor.fiberClassesMap F = BasedFunctor.fiberClassesMap G := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.ext_apply
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
      exact obj_ext_of_isDiscrete (BasedNatTrans.fiberApp η (unop U) x)

end fiberClassesMap

end SameObjectUniverse

section DifferentObjectUniverses

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}

/-- A based functor into a discrete fibration induces a class-to-object presheaf map after source
classes and target objects are placed in any common ambient universe. -/
@[stacks 02Y2 "size-stable action from fiber classes to discrete fibers",
  stacks 04SI "size-stable action from fiber classes to discrete fibers"]
noncomputable def fiberClassesMap.ulift
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    (Functor.fiberIsoClassPresheaf X.p ⋙
        (uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))) ⟶
      (Y.p.fiberObjectPresheaf ⋙
        (uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))) :=
  BasedFunctor.fiberIsoClassMap.ulift.{w} F ≫
    (Functor.IsDiscreteFibration.fiberClassesIso.ulift.{max w uX} Y.p).hom

/- Data audit: this is the lifted quotient action followed by the lifted canonical comparison for
the discrete target. Its component functions are explicit and introduce no new witness choice. -/

/-- The component of the lifted class-to-object map is the ambient lift of the canonical map
through the induced fiber functor. -/
@[simp]
theorem fiberClassesMap.ulift.app
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Y.p.IsDiscreteFibration] (U : Cᵒᵖ) :
    (BasedFunctor.fiberClassesMap.ulift.{w} F).app U =
      TypeCat.ofHom (Functor.isoClassesToObj.ulift.{w}
        (F.fiberFunctor (unop U))) := by
  apply ConcreteCategory.ext_apply
  intro q
  rcases q with ⟨q⟩
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- On a lifted represented source class, the lifted map returns the lifted image under the
induced fiber functor. -/
@[simp]
theorem fiberClassesMap.ulift.app_mk
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (BasedFunctor.fiberClassesMap.ulift.{w} F).app U
        (ULift.up (Quotient.mk'' x)) =
      ULift.up ((F.fiberFunctor (unop U)).obj x) := by
  rfl

/-- For a discrete fibration, the lifted map induced by the identity is the lifted canonical
comparison from fiber classes to fiber objects. -/
@[simp]
theorem fiberClassesMap.ulift.id
    (X : BasedCategory.{vX, uX} C) [X.p.IsDiscreteFibration] :
    BasedFunctor.fiberClassesMap.ulift.{w} (𝟙 X : X ⥤ᵇ X) =
      (Functor.IsDiscreteFibration.fiberClassesIso.ulift.{w} X.p).hom := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.ext_apply
  intro q
  rcases q with ⟨q⟩
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- Lifted class-to-object maps compose with lifted fiber-object maps after all three object
universes are included in the ambient lift. -/
@[simp]
theorem fiberClassesMap.ulift.comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) [X.p.IsFibered]
    [Y.p.IsDiscreteFibration] [Z.p.IsDiscreteFibration] :
    BasedFunctor.fiberClassesMap.ulift.{max w uY} (F ⋙ G) =
      BasedFunctor.fiberClassesMap.ulift.{max w uZ} F ≫
        BasedFunctor.fiberObjectMap.ulift.{max w uX} G := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.ext_apply
  intro q
  rcases q with ⟨q⟩
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- A based natural transformation into a discrete fibration identifies the induced lifted maps
from fiber classes to target fiber objects. -/
theorem fiberClassesMap.ulift.eq_of_hom
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Y.p.IsDiscreteFibration] (η : F ⟶ G) :
    BasedFunctor.fiberClassesMap.ulift.{w} F =
      BasedFunctor.fiberClassesMap.ulift.{w} G := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.ext_apply
  intro q
  rcases q with ⟨q⟩
  induction q using Quotient.inductionOn with
  | h x =>
      exact congrArg ULift.up
        (obj_ext_of_isDiscrete (BasedNatTrans.fiberApp η (unop U) x))

end DifferentObjectUniverses

end BasedFunctor

end CategoryTheory
