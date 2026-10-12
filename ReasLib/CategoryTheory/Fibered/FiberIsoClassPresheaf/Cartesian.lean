/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids

/-!
# Cartesian action on fiberwise isomorphism classes

This leaf supplies the functorial action of cartesian based functors on the
fiberwise isomorphism-class presheaf. The unlifted map only requires the source
and target object types to share a universe; their morphism universes may differ.
For unrelated object universes, `fiberIsoClassMap.ulift` places both presheaves
in a chosen common ambient universe and remains composable after a common lift.
-/

@[expose] public section

universe w u v uS uS₁ uS₂ uS₃ vS₁ vS₂ vS₃

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace CartesianBasedFunctor

section SameObjectUniverse

variable {S₁ S₂ S₃ : Type uS}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂] [Category.{vS₃} S₃]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} {p₃ : S₃ ⥤ C}

/-- A cartesian based functor induces a map between fiberwise isomorphism-class presheaves.
Cartesian preservation is exactly the hypothesis ensuring compatibility with reindexing. -/
noncomputable def fiberIsoClassMap
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] :
    Functor.fiberIsoClassPresheaf p₁ ⟶ Functor.fiberIsoClassPresheaf p₂ where
  app U := TypeCat.ofHom (F.fiberFunctor (unop U)).isoClassesMap
  naturality := fun {_ _} _ ↦ sorry
/- Data audit: each component is the explicit universe-polymorphic quotient map induced by
`F.fiberFunctor`. The deferred naturality field is Prop-valued and is the only new proof debt. -/

namespace fiberIsoClassMap

/-- The component of the cartesian map is the map induced by the ordinary fiber functor. -/
@[simp]
theorem app
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] (U : Cᵒᵖ) :
    (CartesianBasedFunctor.fiberIsoClassMap F).app U =
      TypeCat.ofHom (F.fiberFunctor (unop U)).isoClassesMap := sorry

/-- On a represented fiber component, the induced presheaf map applies the induced fiber functor. -/
@[simp]
theorem app_mk
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (U : Cᵒᵖ) (x : p₁.Fiber (unop U)) :
    ((CartesianBasedFunctor.fiberIsoClassMap F).app U) (Quotient.mk'' x) =
      Quotient.mk'' ((F.fiberFunctor (unop U)).obj x) := sorry

/-- The fiberwise isomorphism-class map induced by an identity cartesian based functor is the
identity. -/
@[simp]
theorem id
    (p : S₁ ⥤ C) [p.IsFibered] :
    CartesianBasedFunctor.fiberIsoClassMap (CartesianBasedFunctor.id p) =
      𝟙 (Functor.fiberIsoClassPresheaf p) := sorry

/-- The map on fiberwise isomorphism-class presheaves induced by a composite is the composite
of the maps induced by its factors. -/
@[simp]
theorem comp
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃)
    [p₁.IsFibered] [p₂.IsFibered] [p₃.IsFibered] :
    CartesianBasedFunctor.fiberIsoClassMap (F.comp G) =
      CartesianBasedFunctor.fiberIsoClassMap F ≫
        CartesianBasedFunctor.fiberIsoClassMap G := sorry

/-- An invertible based natural transformation between cartesian based functors induces equality
of their maps on fiberwise isomorphism classes. No groupoid assumption on the target is needed:
the supplied isomorphism already identifies the two fiber images. -/
theorem eq_of_iso
    {F G : CartesianBasedFunctor p₁ p₂} [p₁.IsFibered] [p₂.IsFibered]
    (e : F.toBasedFunctor ≅ G.toBasedFunctor) :
    CartesianBasedFunctor.fiberIsoClassMap F =
      CartesianBasedFunctor.fiberIsoClassMap G := sorry

/-- Pointwise equality induced by an invertible based transformation. -/
theorem eq_of_iso_app
    {F G : CartesianBasedFunctor p₁ p₂} [p₁.IsFibered] [p₂.IsFibered]
    (e : F.toBasedFunctor ≅ G.toBasedFunctor) (U : Cᵒᵖ) :
    (CartesianBasedFunctor.fiberIsoClassMap F).app U =
      (CartesianBasedFunctor.fiberIsoClassMap G).app U := sorry

/-- A based natural transformation between cartesian based functors into a fibred groupoid target
induces equality of the maps on fiberwise isomorphism classes. -/
theorem eq_of_hom
    {F G : CartesianBasedFunctor p₁ p₂} [p₁.IsFibered]
    [Functor.IsFibered.InGroupoids p₂] (η : F.toBasedFunctor ⟶ G.toBasedFunctor) :
    CartesianBasedFunctor.fiberIsoClassMap F =
      CartesianBasedFunctor.fiberIsoClassMap G := sorry

end fiberIsoClassMap

end SameObjectUniverse

section DifferentObjectUniverses

variable {S₁ : Type uS₁} {S₂ : Type uS₂} {S₃ : Type uS₃}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂] [Category.{vS₃} S₃]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} {p₃ : S₃ ⥤ C}

/-- After a common ambient lift, the maps on fiberwise isomorphism classes induced by a
cartesian based functor commute with restriction in the base. -/
theorem fiberIsoClassMap.ulift.naturality
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Functor.fiberIsoClassPresheaf p₁ ⋙
        (uliftFunctor.{max w uS₁ uS₂, uS₁} :
          Type uS₁ ⥤ Type (max w uS₁ uS₂))).map f ≫
        TypeCat.ofHom (Functor.isoClassesMap.ulift.{w}
          (F.fiberFunctor (unop V))) =
      TypeCat.ofHom (Functor.isoClassesMap.ulift.{w}
          (F.fiberFunctor (unop U))) ≫
        (Functor.fiberIsoClassPresheaf p₂ ⋙
          (uliftFunctor.{max w uS₁ uS₂, uS₂} :
            Type uS₂ ⥤ Type (max w uS₁ uS₂))).map f := sorry

/-- A cartesian based functor between total categories in arbitrary object universes induces a
map of fiberwise isomorphism-class presheaves after lifting both into a common ambient universe.
The additional universe parameter can include further categories before maps are composed. -/
noncomputable def fiberIsoClassMap.ulift
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] :
    (Functor.fiberIsoClassPresheaf p₁ ⋙
        (uliftFunctor.{max w uS₁ uS₂, uS₁} :
          Type uS₁ ⥤ Type (max w uS₁ uS₂))) ⟶
      (Functor.fiberIsoClassPresheaf p₂ ⋙
        (uliftFunctor.{max w uS₁ uS₂, uS₂} :
          Type uS₂ ⥤ Type (max w uS₁ uS₂))) where
  app U := TypeCat.ofHom (Functor.isoClassesMap.ulift.{w}
    (F.fiberFunctor (unop U)))
  naturality := fun {_ _} f ↦ fiberIsoClassMap.ulift.naturality F f

/- Data audit: every component is the clean quotient map `Functor.isoClassesMap.ulift`; only the
Prop-valued naturality field is deferred. -/

/-- On a lifted represented class, the lifted presheaf map applies the induced fiber functor. -/
@[simp]
theorem fiberIsoClassMap.ulift.app_mk
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (U : Cᵒᵖ) (x : p₁.Fiber (unop U)) :
    (fiberIsoClassMap.ulift.{w} F).app U (ULift.up (Quotient.mk'' x)) =
      ULift.up (Quotient.mk'' ((F.fiberFunctor (unop U)).obj x)) := sorry

/-- The identity cartesian based functor induces the identity after an ambient lift. -/
@[simp]
theorem fiberIsoClassMap.ulift.id
    (p : S₁ ⥤ C) [p.IsFibered] :
    fiberIsoClassMap.ulift.{w} (CartesianBasedFunctor.id p) =
      𝟙 (Functor.fiberIsoClassPresheaf p ⋙
        (uliftFunctor.{max w uS₁ uS₁, uS₁} :
          Type uS₁ ⥤ Type (max w uS₁ uS₁))) := sorry

/-- Lifted fiberwise isomorphism-class maps compose after all three total-category object
universes are included in the common ambient lift. -/
@[simp]
theorem fiberIsoClassMap.ulift.comp
    (F : CartesianBasedFunctor p₁ p₂) (G : CartesianBasedFunctor p₂ p₃)
    [p₁.IsFibered] [p₂.IsFibered] [p₃.IsFibered] :
    fiberIsoClassMap.ulift.{max w uS₂} (F.comp G) =
      fiberIsoClassMap.ulift.{max w uS₃} F ≫
        fiberIsoClassMap.ulift.{max w uS₁} G := sorry

/-- Isomorphic cartesian based functors induce the same lifted map on fiberwise isomorphism
classes. -/
theorem fiberIsoClassMap.ulift.eq_of_iso
    {F G : CartesianBasedFunctor p₁ p₂} [p₁.IsFibered] [p₂.IsFibered]
    (e : F.toBasedFunctor ≅ G.toBasedFunctor) :
    fiberIsoClassMap.ulift.{w} F = fiberIsoClassMap.ulift.{w} G := sorry

/-- A based transformation into a fibred groupoid target identifies the induced lifted maps on
fiberwise isomorphism classes. -/
theorem fiberIsoClassMap.ulift.eq_of_hom
    {F G : CartesianBasedFunctor p₁ p₂} [p₁.IsFibered]
    [Functor.IsFibered.InGroupoids p₂] (η : F.toBasedFunctor ⟶ G.toBasedFunctor) :
    fiberIsoClassMap.ulift.{w} F = fiberIsoClassMap.ulift.{w} G := sorry

end DifferentObjectUniverses

end CartesianBasedFunctor

end CategoryTheory
