/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Cartesian
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian

/-!
# Groupoid-target action on fiberwise isomorphism classes

This leaf specializes the cartesian action to arbitrary based functors whose
target is fibred in groupoids, where cartesian preservation is automatic. It
retains the universe-polymorphic interface of the cartesian owner: morphism
universes are independent in the unlifted API, and unrelated object universes
are handled by a common ambient lift.
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

/-- A based functor into a category fibred in groupoids induces the canonical map between
fiberwise isomorphism-class presheaves. Cartesian preservation is supplied by the target
groupoid-fibration property. -/
noncomputable def fiberIsoClassMap
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] :
    Functor.fiberIsoClassPresheaf X.p ⟶ Functor.fiberIsoClassPresheaf Y.p :=
  CartesianBasedFunctor.fiberIsoClassMap
    (CartesianBasedFunctor.ofTargetInGroupoids F)

namespace fiberIsoClassMap

/-- The component of the groupoid-target map is the map induced by the ordinary fiber functor. -/
@[simp]
theorem app
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] (U : Cᵒᵖ) :
    (BasedFunctor.fiberIsoClassMap F).app U =
      TypeCat.ofHom (F.fiberFunctor (unop U)).isoClassesMap := sorry

/-- On a represented fiber component, the groupoid-target map applies the induced fiber functor. -/
@[simp]
theorem app_mk
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    ((BasedFunctor.fiberIsoClassMap F).app U) (Quotient.mk'' x) =
      Quotient.mk'' ((F.fiberFunctor (unop U)).obj x) := sorry

/-- The map on fiberwise isomorphism classes induced by an identity based functor is the identity. -/
@[simp]
theorem id
    (X : BasedCategory.{vX, uS} C) [Functor.IsFibered.InGroupoids X.p] :
    BasedFunctor.fiberIsoClassMap (𝟙 X : X ⥤ᵇ X) =
      𝟙 (Functor.fiberIsoClassPresheaf X.p) := sorry

/-- The map on fiberwise isomorphism classes induced by a composite is the composite of the maps
induced by its factors. -/
@[simp]
theorem comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) [X.p.IsFibered]
    [Functor.IsFibered.InGroupoids Y.p] [Functor.IsFibered.InGroupoids Z.p] :
    BasedFunctor.fiberIsoClassMap (F ⋙ G) =
      BasedFunctor.fiberIsoClassMap F ≫ BasedFunctor.fiberIsoClassMap G := sorry

/-- A based natural transformation into a fibred groupoid target induces equality of the maps
on fiberwise isomorphism classes. -/
theorem eq_of_hom
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] (η : F ⟶ G) :
    BasedFunctor.fiberIsoClassMap F = BasedFunctor.fiberIsoClassMap G := sorry

/-- Pointwise equality induced by a based transformation into a fibred groupoid. -/
theorem eq_of_hom_app
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p]
    (η : F ⟶ G) (U : Cᵒᵖ) :
    (BasedFunctor.fiberIsoClassMap F).app U =
      (BasedFunctor.fiberIsoClassMap G).app U := sorry

end fiberIsoClassMap

end SameObjectUniverse

section DifferentObjectUniverses

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}

/-- A based functor into a groupoid fibration induces a map on fiberwise isomorphism classes
after source and target are lifted into a common ambient universe. The extra universe parameter
can include further categories before these maps are composed. -/
noncomputable def fiberIsoClassMap.ulift
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] :
    (Functor.fiberIsoClassPresheaf X.p ⋙
        (uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))) ⟶
      (Functor.fiberIsoClassPresheaf Y.p ⋙
        (uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))) :=
  CartesianBasedFunctor.fiberIsoClassMap.ulift.{w}
    (CartesianBasedFunctor.ofTargetInGroupoids F)

/- Data audit: this is a thin specialization of the explicit cartesian owner. It introduces no
new witness choice or proof field. -/

/-- On a lifted represented class, the lifted groupoid-target map applies the induced fiber
functor. -/
@[simp]
theorem fiberIsoClassMap.ulift.app_mk
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (fiberIsoClassMap.ulift.{w} F).app U (ULift.up (Quotient.mk'' x)) =
      ULift.up (Quotient.mk'' ((F.fiberFunctor (unop U)).obj x)) := sorry

/-- The identity based functor induces the identity after an ambient lift. -/
@[simp]
theorem fiberIsoClassMap.ulift.id
    (X : BasedCategory.{vX, uX} C) [Functor.IsFibered.InGroupoids X.p] :
    fiberIsoClassMap.ulift.{w} (𝟙 X : X ⥤ᵇ X) =
      𝟙 (Functor.fiberIsoClassPresheaf X.p ⋙
        (uliftFunctor.{max w uX uX, uX} :
          Type uX ⥤ Type (max w uX uX))) := sorry

/-- Lifted groupoid-target maps preserve composition after all three object universes are
included in the common ambient lift. -/
@[simp]
theorem fiberIsoClassMap.ulift.comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) [X.p.IsFibered]
    [Functor.IsFibered.InGroupoids Y.p] [Functor.IsFibered.InGroupoids Z.p] :
    fiberIsoClassMap.ulift.{max w uY} (F ⋙ G) =
      fiberIsoClassMap.ulift.{max w uZ} F ≫
        fiberIsoClassMap.ulift.{max w uX} G := sorry

/-- A based transformation into a fibred groupoid identifies the induced lifted maps on
fiberwise isomorphism classes. -/
theorem fiberIsoClassMap.ulift.eq_of_hom
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] (η : F ⟶ G) :
    fiberIsoClassMap.ulift.{w} F = fiberIsoClassMap.ulift.{w} G := sorry

end DifferentObjectUniverses

end BasedFunctor

end CategoryTheory
