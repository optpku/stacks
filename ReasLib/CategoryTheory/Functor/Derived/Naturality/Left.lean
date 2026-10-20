/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Naturality of Total Left-Derived Functors

This file specializes Mathlib's universal naturality construction to the chosen total
left-derived functors.  The localization, inverted class, and source transformation are the only
explicit inputs needed by downstream users.
-/

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftDerived

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- The map between chosen total left-derived functors induced by a natural transformation. -/
@[stacks 05T2]
noncomputable def mapNatTrans
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    F.totalLeftDerived L S ⟶ G.totalLeftDerived L S :=
  Functor.leftDerivedNatTrans
    (F.totalLeftDerived L S) (G.totalLeftDerived L S)
    (F.totalLeftDerivedCounit L S) (G.totalLeftDerivedCounit L S) S τ

/-- The left-derived map is characterized by compatibility with the total derived counits. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem mapNatTrans.fac
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    whiskerLeft L (mapNatTrans L S τ) ≫ G.totalLeftDerivedCounit L S =
      F.totalLeftDerivedCounit L S ≫ τ := sorry

/-- Objectwise compatibility of the left-derived map with the total derived counits. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem mapNatTrans.fac_app
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] (X : C) :
    (mapNatTrans L S τ).app (L.obj X) ≫ (G.totalLeftDerivedCounit L S).app X =
      (F.totalLeftDerivedCounit L S).app X ≫ τ.app X := sorry

/-- The total left-derived map induced by an identity transformation is the identity. -/
@[stacks 05T2, simp]
theorem mapNatTrans.id
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] :
    mapNatTrans L S (𝟙 F) = 𝟙 (F.totalLeftDerived L S) := sorry

/-- Total left-derived maps preserve composition of source natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.comp
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (τ : F ⟶ G) (σ : G ⟶ K) [L.IsLocalization S]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [K.HasLeftDerivedFunctor S] :
    mapNatTrans L S (τ ≫ σ) = mapNatTrans L S τ ≫ mapNatTrans L S σ := sorry

/- An invertible natural transformation is enough to expose the corresponding derived
invertibility without forcing callers to manufacture an `Iso`. -/
/-- A total left-derived map induced by an invertible natural transformation is invertible. -/
@[stacks 05T2 "isomorphism preservation"]
theorem mapNatTrans_isIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (τ : F ⟶ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [IsIso τ] :
    IsIso (mapNatTrans L S τ) := sorry

/-- The isomorphism between chosen total left-derived functors induced by a natural
isomorphism. -/
@[stacks 05T2]
noncomputable def mapNatIso
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    F.totalLeftDerived L S ≅ G.totalLeftDerived L S :=
  Functor.leftDerivedNatIso
    (F.totalLeftDerived L S) (G.totalLeftDerived L S)
    (F.totalLeftDerivedCounit L S) (G.totalLeftDerivedCounit L S) S e

/-- The hom of the induced total left-derived isomorphism is `mapNatTrans` on the hom. -/
@[stacks 05T2, simp]
theorem mapNatIso.hom
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    (mapNatIso L S e).hom = mapNatTrans L S e.hom := sorry

/-- The inverse of the induced total left-derived isomorphism is `mapNatTrans` on the inverse. -/
@[stacks 05T2, simp]
theorem mapNatIso.inv
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    (mapNatIso L S e).inv = mapNatTrans L S e.inv := sorry

/-- Total left-derived natural isomorphisms preserve reflexivity. -/
@[stacks 05T2, simp]
theorem mapNatIso.refl
    (L : C ⥤ D) (S : MorphismProperty C) (F : C ⥤ E)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] :
    mapNatIso L S (Iso.refl F) = Iso.refl (F.totalLeftDerived L S) := sorry

/-- Total left-derived natural isomorphisms preserve symmetry. -/
@[stacks 05T2, simp]
theorem mapNatIso.symm
    (L : C ⥤ D) (S : MorphismProperty C) {F G : C ⥤ E} (e : F ≅ G)
    [L.IsLocalization S] [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S] :
    mapNatIso L S e.symm = (mapNatIso L S e).symm := sorry

/-- Total left-derived natural isomorphisms preserve transitivity. -/
@[stacks 05T2, simp]
theorem mapNatIso.trans
    (L : C ⥤ D) (S : MorphismProperty C) {F G K : C ⥤ E}
    (e : F ≅ G) (e' : G ≅ K) [L.IsLocalization S]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [K.HasLeftDerivedFunctor S] :
    mapNatIso L S (e ≪≫ e') = mapNatIso L S e ≪≫ mapNatIso L S e' := sorry

end CategoryTheory.Functor.LeftDerived
