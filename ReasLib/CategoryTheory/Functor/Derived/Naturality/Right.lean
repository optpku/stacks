/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Total Right-Derived Functors

This file specializes Mathlib's universal naturality construction to the chosen total
right-derived functors.  The localization, inverted class, and source transformation are the
only explicit inputs needed by downstream users.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- The map between chosen total right-derived functors induced by a natural transformation. -/
@[stacks 05T2]
noncomputable def mapNatTrans
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    F.totalRightDerived L S ⟶ G.totalRightDerived L S :=
  Functor.rightDerivedNatTrans
    (F.totalRightDerived L S) (G.totalRightDerived L S)
    (F.totalRightDerivedUnit L S) (G.totalRightDerivedUnit L S) S τ

/-- The right-derived map is characterized by compatibility with the total derived units. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem mapNatTrans.fac
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    F.totalRightDerivedUnit L S ≫ whiskerLeft L (mapNatTrans L S τ) =
      τ ≫ G.totalRightDerivedUnit L S := sorry

/-- Objectwise compatibility of the right-derived map with the total derived units. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem mapNatTrans.fac_app
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] (X : C) :
    (F.totalRightDerivedUnit L S).app X ≫ (mapNatTrans L S τ).app (L.obj X) =
      τ.app X ≫ (G.totalRightDerivedUnit L S).app X := sorry

/-- The total right-derived map induced by an identity transformation is the identity. -/
@[stacks 05T2, simp]
theorem mapNatTrans.id
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] :
    mapNatTrans L S (𝟙 F) = 𝟙 (F.totalRightDerived L S) := sorry

/-- Total right-derived maps preserve composition of source natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.comp
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (τ : F ⟶ G) (σ : G ⟶ K) [L.IsLocalization S]
    [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S]
    [K.HasRightDerivedFunctor S] :
    mapNatTrans L S (τ ≫ σ) = mapNatTrans L S τ ≫ mapNatTrans L S σ := sorry

/- An invertible natural transformation is enough to expose the corresponding derived
invertibility without forcing callers to manufacture an `Iso`. -/
/-- A total right-derived map induced by an invertible natural transformation is invertible. -/
@[stacks 05T2 "isomorphism preservation"]
theorem mapNatTrans_isIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S]
    [IsIso τ] :
    IsIso (mapNatTrans L S τ) := sorry

/-- The isomorphism between chosen total right-derived functors induced by a natural
isomorphism. -/
@[stacks 05T2]
noncomputable def mapNatIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    F.totalRightDerived L S ≅ G.totalRightDerived L S :=
  Functor.rightDerivedNatIso
    (F.totalRightDerived L S) (G.totalRightDerived L S)
    (F.totalRightDerivedUnit L S) (G.totalRightDerivedUnit L S) S e

/-- The hom of the induced total right-derived isomorphism is `mapNatTrans` on the hom. -/
@[stacks 05T2, simp]
theorem mapNatIso.hom
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    (mapNatIso L S e).hom = mapNatTrans L S e.hom := sorry

/-- The inverse of the induced total right-derived isomorphism is `mapNatTrans` on the inverse. -/
@[stacks 05T2, simp]
theorem mapNatIso.inv
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    (mapNatIso L S e).inv = mapNatTrans L S e.inv := sorry

/-- Total right-derived natural isomorphisms preserve reflexivity. -/
@[stacks 05T2, simp]
theorem mapNatIso.refl
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] :
    mapNatIso L S (Iso.refl F) = Iso.refl (F.totalRightDerived L S) := sorry

/-- Total right-derived natural isomorphisms preserve symmetry. -/
@[stacks 05T2, simp]
theorem mapNatIso.symm
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S] :
    mapNatIso L S e.symm = (mapNatIso L S e).symm := sorry

/-- Total right-derived natural isomorphisms preserve transitivity. -/
@[stacks 05T2, simp]
theorem mapNatIso.trans
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (e : F ≅ G) (e' : G ≅ K) [L.IsLocalization S]
    [F.HasRightDerivedFunctor S] [G.HasRightDerivedFunctor S]
    [K.HasRightDerivedFunctor S] :
    mapNatIso L S (e ≪≫ e') = mapNatIso L S e ≪≫ mapNatIso L S e' := sorry



end CategoryTheory.Functor.RightDerived
