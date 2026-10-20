/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.InducedTopology

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {U : Over S}
  (f : ofOver U ⟶ Y) [Etale f]

/-- An étale morphism from a scheme to an algebraic space is representably étale. -/
theorem localizationObject_isEtale : Representable.Etale f := sorry

/-- An étale morphism from a scheme defines an object of the target's small étale site. -/
def localizationObject : site Y :=
  MorphismProperty.CostructuredArrow.mk ⊤ f (localizationObject_isEtale f)

/-- A chart of a scheme maps canonically to that scheme as a chart of the target. -/
noncomputable def localizationHom (V : site (ofOver U)) :
    (postcompose f (localizationObject_isEtale f)).obj V ⟶ localizationObject f :=
  MorphismProperty.CostructuredArrow.homMk (yoneda.preimage V.hom) trivial (by sorry)

/-- The canonical arrows from charts to the localization object commute with chart maps. -/
theorem localizationHom_naturality {V W : site (ofOver U)} (g : V ⟶ W) :
    (postcompose f (localizationObject_isEtale f)).map g ≫ localizationHom f W =
      localizationHom f V := sorry

/-- Postcomposition with an étale scheme chart gives a functor to the slice small étale site. -/
noncomputable def localizationFunctor : site (ofOver U) ⥤ Over (localizationObject f) :=
  (postcompose f (localizationObject_isEtale f)).toOver (localizationObject f)
    (localizationHom f) (localizationHom_naturality f)

/-- Localization retains the underlying scheme over the base of each chart. -/
theorem localizationFunctor_obj_left (V : site (ofOver U)) :
    ((localizationFunctor f).obj V).left.left = V.left := rfl

/-- The small étale category of a scheme chart is equivalent to the slice at that chart. -/
instance localizationFunctor_isEquivalence : (localizationFunctor f).IsEquivalence := sorry

/-- The small étale topology of a scheme chart is the topology induced from the slice site. -/
theorem localizationTopology_eq :
    topology (ofOver U) =
      (localizationFunctor f).inducedTopology ((topology Y).over (localizationObject f)) :=
  sorry

/-- Identity maps on global sections compare the restricted structure sheaf with the
structure sheaf of the scheme chart. -/
noncomputable def localizationStructureSheafMap :
    (localizationFunctor f).op ⋙ ((structureSheaf Y).over (localizationObject f)).obj ⟶
      (structureSheaf (ofOver U)).obj where
  app V := 𝟙 _
  naturality := by sorry

/-- The structure-sheaf comparison is the identity on the ring of sections of each chart. -/
theorem localizationStructureSheafMap_app (V : (site (ofOver U))ᵒᵖ) :
    (localizationStructureSheafMap f).app V =
      𝟙 ((structureSheaf (ofOver U)).obj.obj V) := rfl

/-- The identity-on-sections comparison of structure presheaves is invertible. -/
instance localizationStructureSheafMap_isIso : IsIso (localizationStructureSheafMap f) := by
  refine ⟨⟨{ app := fun V => 𝟙 _, naturality := ?_ }, ?_, ?_⟩⟩
  · intro V W g
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    simp only [Category.comp_id, Category.id_comp]
    rfl
  · apply NatTrans.ext
    funext V
    exact Category.id_comp _
  · apply NatTrans.ext
    funext V
    exact Category.id_comp _

/-- The small étale ringed site of an étale scheme chart is its target's localized ringed
site: localization is an equivalence, transports the topology, and identifies structure
presheaves by identity maps on sections. -/
theorem ringedLocalization :
    (localizationFunctor f).IsEquivalence ∧
      topology (ofOver U) =
        (localizationFunctor f).inducedTopology ((topology Y).over (localizationObject f)) ∧
      IsIso (localizationStructureSheafMap f) :=
  ⟨localizationFunctor_isEquivalence f, localizationTopology_eq f,
    localizationStructureSheafMap_isIso f⟩

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
