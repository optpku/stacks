/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion

/-!
# Morphism action of set-valued completion

The set-valued completion of a natural transformation is induced by `limMap` of left
whiskering with each truncation tower. Completion preserves pullbacks, yielding a
canonical comparison from the completion of a pullback to the pullback of the
completions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
/-- The limit maps induced by a natural transformation commute with the maps of
completed functors induced by complete local algebra morphisms. -/
private theorem typesCompletionMap_naturality
    {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G)
    {S T : CompleteLocalAlgCat Λ k} (h : S ⟶ T) :
    (typesCompletion F).map h ≫ limMap (whiskerLeft T.truncationSystem α) =
      limMap (whiskerLeft S.truncationSystem α) ≫ (typesCompletion G).map h := by
  apply limit.hom_ext
  intro j
  simpa only [typesCompletion, Category.assoc, limMap_π, limMap_π_assoc,
    whiskerLeft_app, whiskerRight_app, Functor.comp_obj] using
    congrArg (limit.π (S.truncationSystem ⋙ F) j ≫ ·)
      (α.naturality ((CompleteLocalAlgCat.truncationSystemMap h).app j))

/-- The set-valued completion of a natural transformation `α : F ⟶ G`, with component at
a complete local algebra `S` given by `limMap` of `α` whiskered by the truncation tower of
`S`. -/
def typesCompletionMap {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G) :
    typesCompletion F ⟶ typesCompletion G where
  app S := limMap (whiskerLeft S.truncationSystem α)
  naturality {_ _} h := private typesCompletionMap_naturality α h

/-- The component of `typesCompletionMap α` at `S` is `limMap` of the left whiskering of
`α` by the truncation tower of `S`. -/
theorem typesCompletionMap_app {F G : ArtinianLocalAlgCat Λ k ⥤ Type w} (α : F ⟶ G)
    (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionMap α).app S = limMap (whiskerLeft S.truncationSystem α) := rfl

/-- Set-valued completion preserves identity natural transformations. -/
theorem typesCompletionMap_id (F : ArtinianLocalAlgCat Λ k ⥤ Type w) :
    typesCompletionMap (𝟙 F) = 𝟙 (typesCompletion F) := by
  apply NatTrans.ext
  funext S
  change limMap (whiskerLeft S.truncationSystem (𝟙 F)) = 𝟙 _
  rw [whiskerLeft_id']
  exact (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w).map_id _

/-- Set-valued completion preserves composition of natural transformations. -/
theorem typesCompletionMap_comp {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (α : F ⟶ G) (β : G ⟶ H) :
    typesCompletionMap (α ≫ β) = typesCompletionMap α ≫ typesCompletionMap β := by
  apply NatTrans.ext
  funext S
  change limMap (whiskerLeft S.truncationSystem (α ≫ β)) =
    limMap (whiskerLeft S.truncationSystem α) ≫ limMap (whiskerLeft S.truncationSystem β)
  rw [whiskerLeft_comp]
  exact (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w).map_comp _ _

/-- The component at a complete local algebra `S` of the comparison identifying the
completion of a pullback with the pullback of the completions. -/
def typesCompletionPullbackIsoApp {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletion (pullback f g)).obj S ≅
      (pullback (typesCompletionMap f) (typesCompletionMap g)).obj S :=
  HasLimit.isoOfNatIso
      (PreservesPullback.iso
        ((whiskeringLeft ℕᵒᵖ (ArtinianLocalAlgCat Λ k) (Type w)).obj S.truncationSystem) f g) ≪≫
    PreservesPullback.iso (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w)
      (whiskerLeft S.truncationSystem f) (whiskerLeft S.truncationSystem g) ≪≫
    (PreservesPullback.iso ((evaluation (CompleteLocalAlgCat Λ k) (Type w)).obj S)
      (typesCompletionMap f) (typesCompletionMap g)).symm

/-- The hom-component of `typesCompletionPullbackIsoApp` is the composite of the
whiskering, limit, and evaluation pullback-preservation isomorphisms. -/
theorem typesCompletionPullbackIsoApp_hom {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionPullbackIsoApp f g S).hom =
      (HasLimit.isoOfNatIso
          (PreservesPullback.iso
            ((whiskeringLeft ℕᵒᵖ (ArtinianLocalAlgCat Λ k) (Type w)).obj
              S.truncationSystem) f g)).hom ≫
        (PreservesPullback.iso (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w)
          (whiskerLeft S.truncationSystem f) (whiskerLeft S.truncationSystem g)).hom ≫
        (PreservesPullback.iso ((evaluation (CompleteLocalAlgCat Λ k) (Type w)).obj S)
          (typesCompletionMap f) (typesCompletionMap g)).inv := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem typesCompletionPullbackIsoApp_hom_fst
    {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionPullbackIsoApp f g S).hom ≫
        (pullback.fst (typesCompletionMap f) (typesCompletionMap g)).app S =
      (typesCompletionMap (pullback.fst f g)).app S := by
  simp only [typesCompletionPullbackIsoApp, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [PreservesPullback.iso_inv_fst
    ((evaluation (CompleteLocalAlgCat Λ k) (Type w)).obj S)
      (typesCompletionMap f) (typesCompletionMap g),
    PreservesPullback.iso_hom_fst (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w)]
  change limMap _ ≫ limMap _ = limMap _
  erw [← lim.map_comp]
  exact congrArg limMap (PreservesPullback.iso_hom_fst
    ((whiskeringLeft ℕᵒᵖ (ArtinianLocalAlgCat Λ k) (Type w)).obj S.truncationSystem) f g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem typesCompletionPullbackIsoApp_hom_snd
    {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionPullbackIsoApp f g S).hom ≫
        (pullback.snd (typesCompletionMap f) (typesCompletionMap g)).app S =
      (typesCompletionMap (pullback.snd f g)).app S := by
  simp only [typesCompletionPullbackIsoApp, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [PreservesPullback.iso_inv_snd
    ((evaluation (CompleteLocalAlgCat Λ k) (Type w)).obj S)
      (typesCompletionMap f) (typesCompletionMap g),
    PreservesPullback.iso_hom_snd (lim : (ℕᵒᵖ ⥤ Type w) ⥤ Type w)]
  change limMap _ ≫ limMap _ = limMap _
  erw [← lim.map_comp]
  exact congrArg limMap (PreservesPullback.iso_hom_snd
    ((whiskeringLeft ℕᵒᵖ (ArtinianLocalAlgCat Λ k) (Type w)).obj S.truncationSystem) f g)

/-- Naturality of the componentwise pullback-preservation comparison for set-valued
completion. -/
theorem typesCompletionPullbackIso_naturality {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) {S T : CompleteLocalAlgCat Λ k} (h : S ⟶ T) :
    (typesCompletion (pullback f g)).map h ≫ (typesCompletionPullbackIsoApp f g T).hom =
      (typesCompletionPullbackIsoApp f g S).hom ≫
        (pullback (typesCompletionMap f) (typesCompletionMap g)).map h := by
  let E := (evaluation (CompleteLocalAlgCat Λ k) (Type w)).obj T
  apply (cancel_mono (PreservesPullback.iso E
    (typesCompletionMap f) (typesCompletionMap g)).hom).1
  apply pullback.hom_ext
  · simp only [Category.assoc, PreservesPullback.iso_hom_fst]
    change (typesCompletion (pullback f g)).map h ≫
        (typesCompletionPullbackIsoApp f g T).hom ≫
          (pullback.fst (typesCompletionMap f) (typesCompletionMap g)).app T =
      (typesCompletionPullbackIsoApp f g S).hom ≫
        (pullback (typesCompletionMap f) (typesCompletionMap g)).map h ≫
          (pullback.fst (typesCompletionMap f) (typesCompletionMap g)).app T
    rw [(pullback.fst (typesCompletionMap f) (typesCompletionMap g)).naturality,
      typesCompletionPullbackIsoApp_hom_fst, ← Category.assoc,
      typesCompletionPullbackIsoApp_hom_fst]
    exact (typesCompletionMap (pullback.fst f g)).naturality h
  · simp only [Category.assoc, PreservesPullback.iso_hom_snd]
    change (typesCompletion (pullback f g)).map h ≫
        (typesCompletionPullbackIsoApp f g T).hom ≫
          (pullback.snd (typesCompletionMap f) (typesCompletionMap g)).app T =
      (typesCompletionPullbackIsoApp f g S).hom ≫
        (pullback (typesCompletionMap f) (typesCompletionMap g)).map h ≫
          (pullback.snd (typesCompletionMap f) (typesCompletionMap g)).app T
    rw [(pullback.snd (typesCompletionMap f) (typesCompletionMap g)).naturality,
      typesCompletionPullbackIsoApp_hom_snd, ← Category.assoc,
      typesCompletionPullbackIsoApp_hom_snd]
    exact (typesCompletionMap (pullback.snd f g)).naturality h

/-- The canonical isomorphism `typesCompletion (pullback f g) ≅ pullback (typesCompletionMap f)
(typesCompletionMap g)` coming from preservation of limits by whiskering and by `lim`. -/
def typesCompletionPullbackIso {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) :
    typesCompletion (pullback f g) ≅ pullback (typesCompletionMap f) (typesCompletionMap g) :=
  NatIso.ofComponents (fun S ↦ typesCompletionPullbackIsoApp f g S)
    (typesCompletionPullbackIso_naturality f g)

/-- The hom-component of `typesCompletionPullbackIso` at `S` is
`typesCompletionPullbackIsoApp`. -/
theorem typesCompletionPullbackIso_hom {F G H : ArtinianLocalAlgCat Λ k ⥤ Type w}
    (f : F ⟶ H) (g : G ⟶ H) (S : CompleteLocalAlgCat Λ k) :
    (typesCompletionPullbackIso f g).hom.app S =
      (typesCompletionPullbackIsoApp f g S).hom := rfl

end CategoryTheory.Functor
