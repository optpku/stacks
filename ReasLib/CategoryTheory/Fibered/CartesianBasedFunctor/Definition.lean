/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Property
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Cartesian functors between categories over a base

This module defines the universe-polymorphic cartesian-functor owner and its projection and
constructor API. Identity, composition, and equivalence-specific constructors live in separate
leaves.
-/

@[expose] public section

universe u v uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The category of universe-polymorphic cartesian functors between based categories.

This is the correct owner for morphisms that preserve strongly cartesian arrows when the two
total categories need not live in the same universe. The fixed-universe `FiberedCategoryOver` is
the hom type of the bicategory; this full subcategory is its heterogeneous presentation. Its
morphisms are all vertical based natural transformations, as in the ambient hom-category. -/
@[stacks 02XP "universe-polymorphic cartesian 1-morphisms"]
abbrev CartesianBasedFunctor
    {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
    (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C) :=
  ObjectProperty.FullSubcategory
    ((fun F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂ ↦
        F.PreservesStronglyCartesian) :
      ObjectProperty
        (BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂))

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- The underlying functor over the common base. -/
abbrev toBasedFunctor (F : CartesianBasedFunctor p₁ p₂) :
    BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂ :=
  F.obj

/-- The underlying based functor preserves strongly cartesian arrows. -/
abbrev preservesStronglyCartesian (F : CartesianBasedFunctor p₁ p₂) :
    F.toBasedFunctor.PreservesStronglyCartesian :=
  F.property

/-- Build a cartesian based functor from its underlying based functor and preservation
property. -/
def ofBasedFunctor
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.PreservesStronglyCartesian) : CartesianBasedFunctor p₁ p₂ :=
  ⟨F, hF⟩

/-- The based functor underlying `ofBasedFunctor F hF` is the supplied functor `F`. -/
@[simp]
theorem ofBasedFunctor.toBasedFunctor
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.PreservesStronglyCartesian) :
    (ofBasedFunctor F hF).toBasedFunctor = F := sorry

/-- Forget cartesian preservation while retaining the underlying based functor and all vertical
based natural transformations. -/
abbrev forget (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C) :
    CartesianBasedFunctor p₁ p₂ ⥤
      (BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂) :=
  ObjectProperty.ι _

/-- The based natural transformation underlying a morphism of cartesian based functors. -/
abbrev toBasedNatTrans {F G : CartesianBasedFunctor p₁ p₂} (η : F ⟶ G) :
    F.toBasedFunctor ⟶ G.toBasedFunctor :=
  η.hom

/-- Forget an isomorphism of cartesian based functors to the corresponding isomorphism of
underlying based functors. -/
def toBasedIso {F G : CartesianBasedFunctor p₁ p₂} (e : F ≅ G) :
    F.toBasedFunctor ≅ G.toBasedFunctor :=
  (forget p₁ p₂).mapIso e

/-- The forward component of the underlying based-functor isomorphism is the underlying based
natural transformation. -/
@[simp]
theorem toBasedIso.hom {F G : CartesianBasedFunctor p₁ p₂} (e : F ≅ G) :
    (toBasedIso e).hom = toBasedNatTrans e.hom := sorry

/-- The inverse component of the underlying based-functor isomorphism is the underlying based
natural transformation. -/
@[simp]
theorem toBasedIso.inv {F G : CartesianBasedFunctor p₁ p₂} (e : F ≅ G) :
    (toBasedIso e).inv = toBasedNatTrans e.inv := sorry

/-- Regard a vertical based natural transformation as a morphism of cartesian based functors. -/
def homMk {F G : CartesianBasedFunctor p₁ p₂}
    (η : F.toBasedFunctor ⟶ G.toBasedFunctor) : F ⟶ G :=
  ObjectProperty.homMk η

/-- The based natural transformation underlying `homMk η` is `η`. -/
@[simp]
theorem homMk.toBasedNatTrans {F G : CartesianBasedFunctor p₁ p₂}
    (η : F.toBasedFunctor ⟶ G.toBasedFunctor) :
    toBasedNatTrans (homMk η) = η := sorry

/-- Rebundling the underlying based natural transformation recovers the original morphism. -/
@[simp]
theorem toBasedNatTrans.homMk {F G : CartesianBasedFunctor p₁ p₂} (η : F ⟶ G) :
    homMk (toBasedNatTrans η) = η := sorry

/-- Forgetting the identity morphism gives the identity based natural transformation. -/
@[simp]
theorem toBasedNatTrans.id (F : CartesianBasedFunctor p₁ p₂) :
    toBasedNatTrans (𝟙 F) = 𝟙 F.toBasedFunctor := sorry

/-- Forgetting a composite gives the composite of the underlying based natural
transformations. -/
@[simp]
theorem toBasedNatTrans.comp
    {F G H : CartesianBasedFunctor p₁ p₂} (η : F ⟶ G) (θ : G ⟶ H) :
    toBasedNatTrans (η ≫ θ) = toBasedNatTrans η ≫ toBasedNatTrans θ := sorry

/-- Bundling the identity based natural transformation gives the identity morphism. -/
@[simp]
theorem homMk.id (F : CartesianBasedFunctor p₁ p₂) :
    homMk (𝟙 F.toBasedFunctor) = 𝟙 F := sorry

/-- Bundling a composite of based natural transformations gives the composite of the bundled
morphisms. -/
@[simp]
theorem homMk.comp
    {F G H : CartesianBasedFunctor p₁ p₂}
    (η : F.toBasedFunctor ⟶ G.toBasedFunctor)
    (θ : G.toBasedFunctor ⟶ H.toBasedFunctor) :
    homMk (η ≫ θ) = homMk η ≫ homMk θ := sorry

/-- The underlying functor between the total categories. -/
abbrev toFunctor (F : CartesianBasedFunctor p₁ p₂) : S₁ ⥤ S₂ :=
  F.toBasedFunctor.toFunctor

/-- The functor induced by a cartesian based functor on the fiber over `U`. -/
abbrev fiberFunctor (F : CartesianBasedFunctor p₁ p₂) (U : C) : p₁.Fiber U ⥤ p₂.Fiber U :=
  F.toBasedFunctor.fiberFunctor U

/-- A cartesian based functor sends a strongly cartesian lift over a displayed base arrow to a
strongly cartesian lift over the same arrow. -/
theorem Map.stronglyCartesianOfLift
    (F : CartesianBasedFunctor p₁ p₂) {a b : S₁} {U V : C}
    (f : V ⟶ U) (φ : a ⟶ b) (hφ : p₁.IsStronglyCartesian f φ) :
    p₂.IsStronglyCartesian f (F.toFunctor.map φ) := by
  let transport {a' b' : S₂} (ψ : a' ⟶ b')
      (strong : p₂.IsStronglyCartesian (p₂.map ψ) ψ)
      {R S : C} (k : R ⟶ S) (lift : p₂.IsHomLift k ψ) :
      p₂.IsStronglyCartesian k ψ := by
    cases lift
    exact strong
  have sourceLift : p₁.IsHomLift f φ := hφ.toIsHomLift
  cases sourceLift
  have targetLift : p₂.IsHomLift (p₁.map φ) (F.toFunctor.map φ) :=
    @BasedFunctor.preserves_isHomLift C _ (BasedCategory.ofFunctor p₁)
      (BasedCategory.ofFunctor p₂) F.toBasedFunctor _ _ _ _ (p₁.map φ) φ (.map _)
  exact transport (F.toFunctor.map φ) (F.preservesStronglyCartesian φ hφ) _ targetLift
/- Proof strategy: normalize `f` to `p₁.map φ`, apply
`F.preservesStronglyCartesian`, and transport the target statement back along the based-functor
compatibility equation. -/

end CartesianBasedFunctor

end CategoryTheory

/- Axiom audit: the constructors and projections expose the supplied based-functor data directly,
and `toBasedIso` is the ordinary action of the full-subcategory inclusion on an existing
isomorphism. They introduce no chosen semantic payload. -/
