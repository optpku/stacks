/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

private theorem fiberIsoClass_eq_of_hom
    {S : Type uY} [Category.{vY} S] {p : S ⥤ C}
    [Functor.IsFibered.InGroupoids p] {U : C} {x y : p.Fiber U} (φ : x ⟶ y) :
    (Quotient.mk'' x : isomorphismClasses.obj (Cat.of (p.Fiber U))) =
      Quotient.mk'' y := by
  have cartesianAt {R T : C} {a b : S} (f : R ⟶ T) (g : a ⟶ b)
      (h : p.IsHomLift f g) : p.IsCartesian f g := by
    cases h
    exact Functor.IsFibered.InGroupoids.all_isCartesian g
  letI : p.IsHomLift (𝟙 U) φ.val := φ.property
  letI : p.IsHomLift (𝟙 U) (𝟙 x.val) := IsHomLift.id x.property
  letI : p.IsHomLift (𝟙 U) (𝟙 y.val) := IsHomLift.id y.property
  letI : p.IsCartesian (𝟙 U) φ.val := cartesianAt _ _ φ.property
  obtain ⟨ψ, ⟨hψ, hψφ⟩, _⟩ :=
    Functor.IsCartesian.universal_property (p := p) (f := 𝟙 U) (φ := φ.val) (𝟙 y.val)
  letI := hψ
  have hφψ : φ.val ≫ ψ = 𝟙 x.val := by
    apply Functor.IsCartesian.ext p (𝟙 U) φ.val
    simp only [Category.assoc, hψφ, Category.comp_id, Category.id_comp]
  exact Quotient.sound ⟨{
    hom := φ
    inv := ⟨ψ, hψ⟩
    hom_inv_id := Subtype.ext hφψ
    inv_hom_id := Subtype.ext hψφ }⟩

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
      TypeCat.ofHom (F.fiberFunctor (unop U)).isoClassesMap := rfl

/-- On a represented fiber component, the groupoid-target map applies the induced fiber functor. -/
@[simp]
theorem app_mk
    (F : X ⥤ᵇ Y) [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    ((BasedFunctor.fiberIsoClassMap F).app U) (Quotient.mk'' x) =
      Quotient.mk'' ((F.fiberFunctor (unop U)).obj x) := rfl

/-- The map on fiberwise isomorphism classes induced by an identity based functor is the identity. -/
@[simp]
theorem id
    (X : BasedCategory.{vX, uS} C) [Functor.IsFibered.InGroupoids X.p] :
    BasedFunctor.fiberIsoClassMap (𝟙 X : X ⥤ᵇ X) =
      𝟙 (Functor.fiberIsoClassPresheaf X.p) := by
  ext U a
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk'' (((𝟙 X : X ⥤ᵇ X).fiberFunctor (unop U)).obj x) =
    Quotient.mk'' x
  apply congrArg Quotient.mk''
  exact Subtype.ext rfl

/-- The map on fiberwise isomorphism classes induced by a composite is the composite of the maps
induced by its factors. -/
@[simp]
theorem comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) [X.p.IsFibered]
    [Functor.IsFibered.InGroupoids Y.p] [Functor.IsFibered.InGroupoids Z.p] :
    BasedFunctor.fiberIsoClassMap (F ⋙ G) =
      BasedFunctor.fiberIsoClassMap F ≫ BasedFunctor.fiberIsoClassMap G := by
  ext U a
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk'' (((F ⋙ G).fiberFunctor (unop U)).obj x) =
    Quotient.mk'' ((G.fiberFunctor (unop U)).obj ((F.fiberFunctor (unop U)).obj x))
  apply congrArg Quotient.mk''
  exact Subtype.ext rfl

/-- A based natural transformation into a fibred groupoid target induces equality of the maps
on fiberwise isomorphism classes. -/
theorem eq_of_hom
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] (η : F ⟶ G) :
    BasedFunctor.fiberIsoClassMap F = BasedFunctor.fiberIsoClassMap G := by
  ext U a
  refine Quotient.inductionOn a ?_
  intro x
  change Quotient.mk'' ((F.fiberFunctor (unop U)).obj x) =
    Quotient.mk'' ((G.fiberFunctor (unop U)).obj x)
  exact fiberIsoClass_eq_of_hom (BasedNatTrans.fiberApp η (unop U) x)

/-- Pointwise equality induced by a based transformation into a fibred groupoid. -/
theorem eq_of_hom_app
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p]
    (η : F ⟶ G) (U : Cᵒᵖ) :
    (BasedFunctor.fiberIsoClassMap F).app U =
      (BasedFunctor.fiberIsoClassMap G).app U :=
  congrArg (fun α => α.app U) (eq_of_hom η)

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
      ULift.up (Quotient.mk'' ((F.fiberFunctor (unop U)).obj x)) := rfl

/-- The identity based functor induces the identity after an ambient lift. -/
@[simp]
theorem fiberIsoClassMap.ulift.id
    (X : BasedCategory.{vX, uX} C) [Functor.IsFibered.InGroupoids X.p] :
    fiberIsoClassMap.ulift.{w} (𝟙 X : X ⥤ᵇ X) =
      𝟙 (Functor.fiberIsoClassPresheaf X.p ⋙
        (uliftFunctor.{max w uX uX, uX} :
          Type uX ⥤ Type (max w uX uX))) := by
  ext U a
  rcases a with ⟨a⟩
  refine Quotient.inductionOn a ?_
  intro x
  change ULift.up (Quotient.mk'' (((𝟙 X : X ⥤ᵇ X).fiberFunctor (unop U)).obj x)) =
    ULift.up (Quotient.mk'' x)
  apply congrArg ULift.up
  apply congrArg Quotient.mk''
  exact Subtype.ext rfl

/-- Lifted groupoid-target maps preserve composition after all three object universes are
included in the common ambient lift. -/
@[simp]
theorem fiberIsoClassMap.ulift.comp
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) [X.p.IsFibered]
    [Functor.IsFibered.InGroupoids Y.p] [Functor.IsFibered.InGroupoids Z.p] :
    fiberIsoClassMap.ulift.{max w uY} (F ⋙ G) =
      fiberIsoClassMap.ulift.{max w uZ} F ≫
        fiberIsoClassMap.ulift.{max w uX} G := by
  ext U a
  rcases a with ⟨a⟩
  refine Quotient.inductionOn a ?_
  intro x
  change ULift.up (Quotient.mk'' (((F ⋙ G).fiberFunctor (unop U)).obj x)) =
    ULift.up
      (Quotient.mk'' ((G.fiberFunctor (unop U)).obj ((F.fiberFunctor (unop U)).obj x)))
  apply congrArg ULift.up
  apply congrArg Quotient.mk''
  exact Subtype.ext rfl

/-- A based transformation into a fibred groupoid identifies the induced lifted maps on
fiberwise isomorphism classes. -/
theorem fiberIsoClassMap.ulift.eq_of_hom
    {F G : X ⥤ᵇ Y} [X.p.IsFibered] [Functor.IsFibered.InGroupoids Y.p] (η : F ⟶ G) :
    fiberIsoClassMap.ulift.{w} F = fiberIsoClassMap.ulift.{w} G := by
  ext U a
  rcases a with ⟨a⟩
  refine Quotient.inductionOn a ?_
  intro x
  change ULift.up (Quotient.mk'' ((F.fiberFunctor (unop U)).obj x)) =
    ULift.up (Quotient.mk'' ((G.fiberFunctor (unop U)).obj x))
  apply congrArg ULift.up
  exact fiberIsoClass_eq_of_hom (BasedNatTrans.fiberApp η (unop U) x)

end DifferentObjectUniverses

end BasedFunctor

end CategoryTheory
