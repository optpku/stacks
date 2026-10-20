/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso
public import ReasLib.CategoryTheory.Fibered.Fiber.Hom
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Comparison

/-!
# Cartesian-functor reindexing comparison

This module constructs the objectwise comparison between the fiber functors induced by a
`CartesianBasedFunctor` and the reindexing functors induced by supplied cleavages.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

universe uS₁ vS₁ uS₂ vS₂

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

section ReindexMapIsoImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/- Axiom audit (mathlib 4.32): `#print axioms Reindex.mapIso` contains `sorryAx` while
`Map.stronglyCartesianOfLift` is deferred. The only entry point is the Prop-valued proof that the
image of the source lift is strongly cartesian; `domainIsoOfBaseIso` then feeds that witness to
`IsStronglyCartesian.map` to obtain the non-Prop comparison arrow. Consequently proving
`Map.stronglyCartesianOfLift` is a data-cleanliness priority, not merely a downstream convenience.
-/
/-- The ambient-domain comparison of the two strongly cartesian arrows to `F(x)`. This is a
construction-level implementation of `Reindex.mapIso`; downstream statements should normally
use the bundled comparison.

Mathlib constructs its two maps with `IsStronglyCartesian.map`, i.e. `Classical.choose` applied to
the cartesian universal property. Uniqueness makes this a canonical API-level choice, but the
construction is intentionally noncomputable. -/
private noncomputable def mapIsoAmbient
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (f⁎[χ₂] ((F.fiberFunctor U).obj x)).1 ≅
      ((F.fiberFunctor V).obj (f⁎[χ₁] x)).1 :=
  Functor.IsStronglyCartesian.DomainIso.ofBaseIso (g := Iso.refl V) p₂
    (Category.id_comp f).symm
    (F.toFunctor.map (χ₁.cartesianHom f x))
    (χ₂.cartesianHom f ((F.fiberFunctor U).obj x))
    (Map.stronglyCartesianOfLift F f (χ₁.cartesianHom f x)
      (Functor.Cleavage.cartesianHom.isStronglyCartesian χ₁ f x))
    (Functor.Cleavage.cartesianHom.isStronglyCartesian χ₂ f ((F.fiberFunctor U).obj x))

/-- The forward ambient comparison lies over the identity of the pullback base. -/
private theorem mapIsoAmbientHomIsHomLift
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    p₂.IsHomLift (𝟙 V) (mapIsoAmbient F χ₁ χ₂ f x).hom := sorry
/- Proof strategy: unfold `mapIsoAmbient` and apply
`IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift` to the identity base isomorphism. -/

/-- The inverse ambient comparison lies over the identity of the pullback base. -/
private theorem mapIsoAmbientInvIsHomLift
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    p₂.IsHomLift (𝟙 V) (mapIsoAmbient F χ₁ χ₂ f x).inv := sorry
/- Proof strategy: unfold `mapIsoAmbient` and apply
`IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift` to the identity base isomorphism. -/

/-- The forward comparison packaged as a morphism in the fiber over `V`. -/
private noncomputable def mapHom
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    f⁎[χ₂] ((F.fiberFunctor U).obj x) ⟶
      (F.fiberFunctor V).obj (f⁎[χ₁] x) :=
  Functor.Fiber.Hom.mk (mapIsoAmbient F χ₁ χ₂ f x).hom
    (mapIsoAmbientHomIsHomLift F χ₁ χ₂ f x)

/-- The inverse comparison packaged as a morphism in the fiber over `V`. -/
private noncomputable def mapInv
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (F.fiberFunctor V).obj (f⁎[χ₁] x) ⟶
      f⁎[χ₂] ((F.fiberFunctor U).obj x) :=
  Functor.Fiber.Hom.mk (mapIsoAmbient F χ₁ χ₂ f x).inv
    (mapIsoAmbientInvIsHomLift F χ₁ χ₂ f x)

/-- The construction-level comparison maps compose to the identity in the forward order. -/
private theorem mapHomInvId
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    mapHom F χ₁ χ₂ f x ≫ mapInv F χ₁ χ₂ f x = 𝟙 _ := sorry
/- Proof strategy: use `Functor.Fiber.hom_ext` and the ambient isomorphism's `hom_inv_id`. -/

/-- The construction-level comparison maps compose to the identity in the reverse order. -/
private theorem mapInvHomId
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    mapInv F χ₁ χ₂ f x ≫ mapHom F χ₁ χ₂ f x = 𝟙 _ := sorry
/- Proof strategy: use `Functor.Fiber.hom_ext` and the ambient isomorphism's `inv_hom_id`. -/

end Implementation

/-- The canonical comparison `f⁎[χ₂] (F x) ≅ F (f⁎[χ₁] x)` for a universe-polymorphic
cartesian based functor. Its ambient isomorphism is `IsStronglyCartesian.domainIsoOfBaseIso`; its
maps are selected from the universal property and characterized uniquely, so no project-local raw
existential witness is exposed. -/
noncomputable def Reindex.mapIso
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    f⁎[χ₂] ((F.fiberFunctor U).obj x) ≅
      (F.fiberFunctor V).obj (f⁎[χ₁] x) where
  hom := Implementation.mapHom F χ₁ χ₂ f x
  inv := Implementation.mapInv F χ₁ χ₂ f x
  hom_inv_id := Implementation.mapHomInvId F χ₁ χ₂ f x
  inv_hom_id := Implementation.mapInvHomId F χ₁ χ₂ f x

end ReindexMapIsoImplementation

/-- The forward reindexing comparison is a fiber morphism over the identity of the
reindexed base object. This is the stable total-category readout of its fiber packaging. -/
theorem Reindex.mapIso.hom.isHomLift
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    p₂.IsHomLift (𝟙 V) (Reindex.mapIso F χ₁ χ₂ f x).hom.1 := sorry

/-- The inverse reindexing comparison is a fiber morphism over the identity of the
reindexed base object. This is the stable total-category readout of its fiber packaging. -/
theorem Reindex.mapIso.inv.isHomLift
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    p₂.IsHomLift (𝟙 V) (Reindex.mapIso F χ₁ χ₂ f x).inv.1 := sorry

/-- The forward reindexing comparison is characterized by its factorization through the image of
the chosen source cartesian arrow. -/
theorem Reindex.mapIso.hom.fac
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (Reindex.mapIso F χ₁ χ₂ f x).hom.1 ≫ F.toFunctor.map (χ₁.cartesianHom f x) =
      χ₂.cartesianHom f ((F.fiberFunctor U).obj x) := sorry
/- Proof strategy: unfold only the construction-level ambient comparison, apply
`IsStronglyCartesian.domainIsoOfBaseIso_hom`, and forget the fiber packaging. -/

/-- The inverse reindexing comparison followed by the chosen target cartesian arrow recovers the
image of the chosen source cartesian arrow. -/
theorem Reindex.mapIso.inv.fac
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) (x : p₁.Fiber U) :
    (Reindex.mapIso F χ₁ χ₂ f x).inv.1 ≫
        χ₂.cartesianHom f ((F.fiberFunctor U).obj x) =
      F.toFunctor.map (χ₁.cartesianHom f x) := sorry
/- Proof strategy: precompose `Reindex.mapIso.hom.fac` with the inverse comparison and
cancel the inverse-hom pair. -/

end CartesianBasedFunctor

end CategoryTheory
