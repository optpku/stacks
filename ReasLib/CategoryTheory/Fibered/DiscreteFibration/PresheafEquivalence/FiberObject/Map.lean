module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject.Basic

/-!
# Functoriality of fiber-object presheaves

This module records the natural transformation on fiber-object presheaves induced by a based
functor between discrete fibrations. The construction belongs at the `BasedFunctor` layer; global
straightening functors should use it rather than rebuild its components privately.
-/

@[expose] public section

universe w u v uX uY uZ vX vY vZ

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

section SameUniverse

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uX} C}
variable {Z : BasedCategory.{vZ, uX} C}

/-- The object functions induced on discrete fibers commute with intrinsic reindexing. -/
theorem fiberObjectMap.naturality
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration]
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    X.p.fiberObjectPresheaf.map f ≫
        TypeCat.ofHom (F.fiberFunctor (unop V)).obj =
      TypeCat.ofHom (F.fiberFunctor (unop U)).obj ≫
        Y.p.fiberObjectPresheaf.map f := sorry

/-- A based functor between discrete fibrations induces a natural transformation between their
fiber-object presheaves. -/
@[stacks 02Y2 "based action on fiber-object presheaves",
  stacks 04SI "based action on fiber-object presheaves"]
noncomputable def fiberObjectMap
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration] :
    X.p.fiberObjectPresheaf ⟶ Y.p.fiberObjectPresheaf where
  app U := TypeCat.ofHom (F.fiberFunctor (unop U)).obj
  naturality := fun {_ _} f ↦ fiberObjectMap.naturality F f

/- Axiom audit: every component is the explicit object function of `F.fiberFunctor`; only the
Prop-valued naturality field is deferred. -/

namespace fiberObjectMap

/-- The component of `fiberObjectMap` is the object function of the induced fiber functor. -/
@[simp]
theorem app
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) :
    (fiberObjectMap F).app U =
      TypeCat.ofHom (F.fiberFunctor (unop U)).obj := sorry

/-- Pointwise, `fiberObjectMap` applies the induced fiber functor. -/
@[simp]
theorem app_apply
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (fiberObjectMap F).app U x = (F.fiberFunctor (unop U)).obj x := sorry

/-- Mapping an intrinsically reindexed object is intrinsic reindexing of its image. -/
@[simp]
theorem reindexObj
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration]
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : X.p.Fiber (unop U)) :
    (F.fiberFunctor (unop V)).obj
        (Functor.IsDiscreteFibration.reindexObj X.p f.unop x) =
      Functor.IsDiscreteFibration.reindexObj Y.p f.unop
        ((F.fiberFunctor (unop U)).obj x) := sorry

/-- The identity based functor induces the identity on fiber-object presheaves. -/
@[simp]
theorem id (X : BasedCategory.{vX, uX} C) [X.p.IsDiscreteFibration] :
    fiberObjectMap (BasedFunctor.id X) = 𝟙 X.p.fiberObjectPresheaf := sorry

/-- The fiber-object map induced by a composite is the composite of the induced maps. -/
@[simp]
theorem comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z)
    [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration] [Z.p.IsDiscreteFibration] :
    fiberObjectMap (BasedFunctor.comp F G) =
      fiberObjectMap F ≫ fiberObjectMap G := sorry

end fiberObjectMap

end SameUniverse

section DifferentUniverses

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}

/-- After lifting to a common ambient universe, the object functions induced on discrete fibers
commute with intrinsic reindexing. -/
theorem fiberObjectMap.ulift.naturality
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration]
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (X.p.fiberObjectPresheaf ⋙
        (uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))).map f ≫
        TypeCat.ofHom
          (fun x ↦ ULift.up ((F.fiberFunctor (unop V)).obj x.down)) =
      TypeCat.ofHom
          (fun x ↦ ULift.up ((F.fiberFunctor (unop U)).obj x.down)) ≫
        (Y.p.fiberObjectPresheaf ⋙
          (uliftFunctor.{max w uX uY, uY} :
            Type uY ⥤ Type (max w uX uY))).map f := sorry

/-- A based functor between discrete fibrations in arbitrary total-category universes induces a
map of fiber-object presheaves after a common ambient lift. The extra universe parameter can
include further categories before several maps are composed. -/
@[stacks 02Y2 "size-stable based action on fiber-object presheaves",
  stacks 04SI "size-stable based action on fiber-object presheaves"]
noncomputable def fiberObjectMap.ulift
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration] :
    (X.p.fiberObjectPresheaf ⋙
        (uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))) ⟶
      (Y.p.fiberObjectPresheaf ⋙
        (uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))) where
  app U := TypeCat.ofHom
    (fun x ↦ ULift.up ((F.fiberFunctor (unop U)).obj x.down))
  naturality := fun {_ _} f ↦ fiberObjectMap.ulift.naturality F f

/- Axiom audit: the lifted component functions are explicit compositions of `ULift.up`,
`ULift.down`, and the object maps of `F.fiberFunctor`; only naturality is deferred. -/

/-- On a lifted fiber object, the lifted map applies the induced fiber functor. -/
@[simp]
theorem fiberObjectMap.ulift.app_apply
    (F : X ⥤ᵇ Y) [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (fiberObjectMap.ulift.{w} F).app U (ULift.up x) =
      ULift.up ((F.fiberFunctor (unop U)).obj x) := sorry

/-- The identity based functor induces the identity after an ambient universe lift. -/
@[simp]
theorem fiberObjectMap.ulift.id
    (X : BasedCategory.{vX, uX} C) [X.p.IsDiscreteFibration] :
    fiberObjectMap.ulift.{w} (BasedFunctor.id X) =
      𝟙 (X.p.fiberObjectPresheaf ⋙
        (uliftFunctor.{max w uX uX, uX} :
          Type uX ⥤ Type (max w uX uX))) := sorry

/-- Lifted fiber-object maps compose after all three total-category object universes are included
in the common ambient lift. -/
@[simp]
theorem fiberObjectMap.ulift.comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z)
    [X.p.IsDiscreteFibration] [Y.p.IsDiscreteFibration] [Z.p.IsDiscreteFibration] :
    fiberObjectMap.ulift.{max w uY} (BasedFunctor.comp F G) =
      fiberObjectMap.ulift.{max w uZ} F ≫
        fiberObjectMap.ulift.{max w uX} G := sorry

end DifferentUniverses

end BasedFunctor

end CategoryTheory
