/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.KernelPair
public import ReasLib.CategoryTheory.Groupoid.Quotient
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Canonical morphisms from kernel-pair quotients

A morphism from a set-valued functor to a category cofibered in groupoids induces
a fully faithful morphism from its kernel-pair quotient. This morphism is an
equivalence exactly when the original morphism is essentially surjective.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]
variable {U : C ⥤ Type (max v w)}
variable {F : CofiberedCategoryOver.Groupoids.{u, v, max u (max v w), v} C}

/-- The canonical image of a quotient arrow is the image lift over its base morphism,
followed by endpoint transports and the inverse kernel-pair isomorphism. -/
def quotientMapHom (f : Functor.ofTypeValued U ⟶ F)
    {p q : (ofMorphism f).quotient.total} (φ : p ⟶ q) :
    imageObj f p.base p.fiber ⟶ imageObj f q.base q.fiber :=
  let a : PointHom (ofMorphism f) q.base ((ofMorphism f).U.map φ.base p.fiber) q.fiber :=
    φ.fiber
  imageLift f φ.base p.fiber ≫
    eqToHom (congrArg (imageObj f q.base) a.source.symm) ≫
    a.arrow.inv ≫
    eqToHom (congrArg (imageObj f q.base) a.target)

/-- The canonical arrow action on the kernel-pair quotient preserves identities. -/
theorem quotientMapHom_id (f : Functor.ofTypeValued U ⟶ F)
    (p : (ofMorphism f).quotient.total) :
    quotientMapHom f (𝟙 p) = 𝟙 (imageObj f p.base p.fiber) := sorry

/-- The canonical total functor from the kernel-pair quotient sends each element to its
image and each arrow to the image lift followed by the inverse kernel-pair isomorphism. -/
def quotientMapFunctor (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).quotient.total ⥤ F.total where
  obj p := imageObj f p.base p.fiber
  map φ := quotientMapHom f φ
  map_id := quotientMapHom_id f
  map_comp := sorry

/-- The canonical total functor from the kernel-pair quotient commutes with the
projections to the base category. -/
theorem quotientMapFunctor_w (f : Functor.ofTypeValued U ⟶ F) :
    quotientMapFunctor f ⋙ F.toBasedCategory.p =
      (ofMorphism f).quotient.toBasedCategory.p := sorry

/-- A morphism from a set-valued functor to a cofibered groupoid category induces a
canonical morphism over the base from its kernel-pair quotient. -/
def quotientMap (f : Functor.ofTypeValued U ⟶ F) :
    (ofMorphism f).quotient.toBasedCategory ⥤ᵇ F.toBasedCategory where
  toFunctor := quotientMapFunctor f
  w := quotientMapFunctor_w f

/-- On objects, the canonical quotient morphism sends an element to its image. -/
theorem quotientMap_obj (f : Functor.ofTypeValued U ⟶ F) (T : C) (x : U.obj T) :
    (quotientMap f).obj ⟨T, x⟩ = imageObj f T x := sorry

/-- On arrows, the canonical quotient morphism agrees with the image lift and
kernel-pair isomorphism construction. -/
theorem quotientMap_map (f : Functor.ofTypeValued U ⟶ F)
    {p q : (ofMorphism f).quotient.total} (φ : p ⟶ q) :
    (quotientMap f).map φ = quotientMapHom f φ := rfl

/-- The canonical morphism from a kernel-pair quotient is full. -/
instance quotientMap_full (f : Functor.ofTypeValued U ⟶ F) :
    (quotientMap f).Full := sorry

/-- The canonical morphism from a kernel-pair quotient is faithful. -/
instance quotientMap_faithful (f : Functor.ofTypeValued U ⟶ F) :
    (quotientMap f).Faithful := sorry

/-- The canonical morphism from a kernel-pair quotient is an equivalence over the base
whenever the original morphism is essentially surjective. -/
instance quotientMap_isEquivalence (f : Functor.ofTypeValued U ⟶ F)
    [(CofiberedCategoryOver.Groupoids.toBasedFunctor f).EssSurj] :
    BasedFunctor.IsEquivalence (quotientMap f) := sorry

/-- The canonical morphism from a kernel-pair quotient is fully faithful. -/
theorem quotientMap_fullyFaithful (f : Functor.ofTypeValued U ⟶ F) :
    Nonempty (quotientMap f).FullyFaithful := sorry

/-- The canonical morphism from a kernel-pair quotient is an equivalence over the base
if and only if the original morphism is essentially surjective. -/
theorem quotientMap_isEquivalence_iff (f : Functor.ofTypeValued U ⟶ F) :
    BasedFunctor.IsEquivalence (quotientMap f) ↔
      (CofiberedCategoryOver.Groupoids.toBasedFunctor f).EssSurj := sorry

end CategoryTheory.GroupoidInFunctors
