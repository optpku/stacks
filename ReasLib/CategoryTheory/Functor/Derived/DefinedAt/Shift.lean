/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Transport
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Domain
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift

@[expose] public section

/-!
# Shift Stability of Source-Defined Derived Values

Essential constancy of a localization-indexed diagram is invariant under the reindexing and
target equivalences induced by a shift.  This leaf records that fact independently of additive
or triangulated structures.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits MorphismProperty ObjectProperty

section PresentationTransport

variable {I J C E : Type*} [Category* I] [Category* J] [Category* C] [Category* E]

set_option backward.isDefEq.respectTransparency false in
private theorem right_map {M : I ⥤ C} (hM : IsFiltered.IsEssentiallyConstant M)
    (H : C ⥤ E) : IsFiltered.IsEssentiallyConstant (M ⋙ H) := by
  rcases hM with ⟨c, i, σ, hfac⟩
  refine ⟨H.mapCocone c, i, σ.map H, ?_⟩
  intro j
  rcases hfac j with ⟨k, a, b, h⟩
  refine ⟨k, a, b, ?_⟩
  change H.map (M.map b) = H.map (c.ι.app j) ≫ H.map σ.section_ ≫ H.map (M.map a)
  simpa only [Functor.map_comp] using congrArg H.map h

set_option backward.isDefEq.respectTransparency false in
private theorem left_map {M : I ⥤ C} (hM : IsCofiltered.IsEssentiallyConstant M)
    (H : C ⥤ E) : IsCofiltered.IsEssentiallyConstant (M ⋙ H) := by
  rcases hM with ⟨c, i, σ, hfac⟩
  refine ⟨H.mapCone c, i, σ.map H, ?_⟩
  intro j
  rcases hfac j with ⟨k, a, b, h⟩
  refine ⟨k, a, b, ?_⟩
  change H.map (M.map b) = H.map (M.map a) ≫ H.map σ.retraction ≫ H.map (c.π.app j)
  simpa only [Functor.map_comp] using congrArg H.map h

set_option backward.isDefEq.respectTransparency false in
private theorem right_reindex (e : J ≌ I) {M : I ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant M) :
    IsFiltered.IsEssentiallyConstant (e.functor ⋙ M) := by
  rcases hM with ⟨c, i, σ, hfac⟩
  refine ⟨c.whisker e.functor, e.inverse.obj i,
    { section_ := σ.section_ ≫ M.map (e.counitIso.inv.app i), id := ?_ }, ?_⟩
  · change (σ.section_ ≫ M.map (e.counitIso.inv.app i)) ≫
        c.ι.app (e.functor.obj (e.inverse.obj i)) = 𝟙 c.pt
    have hw : M.map (e.counitIso.inv.app i) ≫
        c.ι.app (e.functor.obj (e.inverse.obj i)) = c.ι.app i :=
      c.w (e.counitIso.inv.app i)
    rw [Category.assoc, hw]
    exact σ.id
  · intro j
    rcases hfac (e.functor.obj j) with ⟨k, a, b, h⟩
    let a' := e.fullyFaithfulFunctor.preimage
      (e.counitIso.hom.app i ≫ a ≫ e.counitIso.inv.app k)
    let b' := e.fullyFaithfulFunctor.preimage (b ≫ e.counitIso.inv.app k)
    refine ⟨e.inverse.obj k, a', b', ?_⟩
    change M.map (e.functor.map b') =
      c.ι.app (e.functor.obj j) ≫ (σ.section_ ≫ M.map (e.counitIso.inv.app i)) ≫
        M.map (e.functor.map a')
    have ha : M.map (e.counitIso.inv.app i) ≫ M.map (e.functor.map a') =
        M.map a ≫ M.map (e.counitIso.inv.app k) := by
      dsimp only [a']
      rw [← M.map_comp, e.fullyFaithfulFunctor.map_preimage]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, M.map_comp]
    have hb : M.map (e.functor.map b') = M.map b ≫ M.map (e.counitIso.inv.app k) := by
      dsimp only [b']
      rw [e.fullyFaithfulFunctor.map_preimage, M.map_comp]
    rw [hb, h]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ c.ι.app (e.functor.obj j) ≫ σ.section_ ≫ t) ha.symm

set_option backward.isDefEq.respectTransparency false in
private theorem left_reindex (e : J ≌ I) {M : I ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant M) :
    IsCofiltered.IsEssentiallyConstant (e.functor ⋙ M) := by
  rcases hM with ⟨c, i, σ, hfac⟩
  refine ⟨c.whisker e.functor, e.inverse.obj i,
    { retraction := M.map (e.counitIso.hom.app i) ≫ σ.retraction, id := ?_ }, ?_⟩
  · change c.π.app (e.functor.obj (e.inverse.obj i)) ≫
        (M.map (e.counitIso.hom.app i) ≫ σ.retraction) = 𝟙 c.pt
    have hw : c.π.app (e.functor.obj (e.inverse.obj i)) ≫
        M.map (e.counitIso.hom.app i) = c.π.app i :=
      c.w (e.counitIso.hom.app i)
    rw [← Category.assoc, hw]
    exact σ.id
  · intro j
    rcases hfac (e.functor.obj j) with ⟨k, a, b, h⟩
    let a' := e.fullyFaithfulFunctor.preimage
      (e.counitIso.hom.app k ≫ a ≫ e.counitIso.inv.app i)
    let b' := e.fullyFaithfulFunctor.preimage (e.counitIso.hom.app k ≫ b)
    refine ⟨e.inverse.obj k, a', b', ?_⟩
    change M.map (e.functor.map b') =
      M.map (e.functor.map a') ≫ (M.map (e.counitIso.hom.app i) ≫ σ.retraction) ≫
        c.π.app (e.functor.obj j)
    have ha : M.map (e.functor.map a') ≫ M.map (e.counitIso.hom.app i) =
        M.map (e.counitIso.hom.app k) ≫ M.map a := by
      dsimp only [a']
      rw [← M.map_comp, e.fullyFaithfulFunctor.map_preimage]
      simp only [Category.assoc, Iso.inv_hom_id_app, M.map_comp]
      change M.map (e.counitIso.hom.app k) ≫ M.map a ≫ M.map (𝟙 i) =
        M.map (e.counitIso.hom.app k) ≫ M.map a
      rw [M.map_id, Category.comp_id]
    have hb : M.map (e.functor.map b') = M.map (e.counitIso.hom.app k) ≫ M.map b := by
      dsimp only [b']
      rw [e.fullyFaithfulFunctor.map_preimage, M.map_comp]
    rw [hb, h]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ σ.retraction ≫ c.π.app (e.functor.obj j)) ha.symm

set_option backward.isDefEq.respectTransparency false in
private theorem right_iso {M N : I ⥤ C} (e : M ≅ N)
    (hM : IsFiltered.IsEssentiallyConstant M) : IsFiltered.IsEssentiallyConstant N := by
  rcases hM with ⟨c, i, σ, hfac⟩
  refine ⟨(Cocone.precompose e.inv).obj c, i,
    { section_ := σ.section_ ≫ e.hom.app i, id := ?_ }, ?_⟩
  · change (σ.section_ ≫ e.hom.app i) ≫ (e.inv.app i ≫ c.ι.app i) = 𝟙 c.pt
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, σ.id]
    rfl
  · intro j
    rcases hfac j with ⟨k, a, b, h⟩
    refine ⟨k, a, b, ?_⟩
    change N.map b = (e.inv.app j ≫ c.ι.app j) ≫ (σ.section_ ≫ e.hom.app i) ≫ N.map a
    calc
      N.map b = e.inv.app j ≫ M.map b ≫ e.hom.app k := by
        rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
      _ = (e.inv.app j ≫ c.ι.app j) ≫ (σ.section_ ≫ e.hom.app i) ≫ N.map a := by
        rw [h]
        simp only [Category.assoc, e.hom.naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem left_iso {M N : I ⥤ C} (e : M ≅ N)
    (hM : IsCofiltered.IsEssentiallyConstant M) : IsCofiltered.IsEssentiallyConstant N := by
  rcases hM with ⟨c, i, σ, hfac⟩
  refine ⟨(Cone.postcompose e.hom).obj c, i,
    { retraction := e.inv.app i ≫ σ.retraction, id := ?_ }, ?_⟩
  · change (c.π.app i ≫ e.hom.app i) ≫ (e.inv.app i ≫ σ.retraction) = 𝟙 c.pt
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, σ.id]
    rfl
  · intro j
    rcases hfac j with ⟨k, a, b, h⟩
    refine ⟨k, a, b, ?_⟩
    change N.map b = N.map a ≫ (e.inv.app i ≫ σ.retraction) ≫ (c.π.app j ≫ e.hom.app j)
    calc
      N.map b = e.inv.app k ≫ M.map b ≫ e.hom.app j := by
        rw [e.hom.naturality, Iso.inv_hom_id_app_assoc]
      _ = N.map a ≫ (e.inv.app i ≫ σ.retraction) ≫ (c.π.app j ≫ e.hom.app j) := by
        rw [h]
        simp only [← Category.assoc, e.inv.naturality]

end PresentationTransport

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.RightDerived.DefinedAt

namespace objects

/-- The object property where the right-derived indexing diagram is essentially constant is
stable under integer shifts. -/
@[stacks 05SC "shift-stable right-derived essential-constancy domain"]
instance isStableUnderShift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (Functor.RightDerived.DefinedAt.objects F S) ℤ where
  isStableUnderShiftBy n := ⟨fun X hX ↦ ⟨right_iso
    (Functor.RightDerived.Value.Shift.diagramIso F S X n)
    (right_reindex (Functor.RightDerived.Value.Shift.indexEquivalence S X n)
      (right_map hX.isEssentiallyConstant (shiftFunctor D' n)))⟩⟩

end objects

/-- Source-definedness of a pointwise right-derived value transports through an integer shift. -/
@[stacks 05SC "right-derived source-definedness after a shift"]
instance shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [Functor.RightDerived.DefinedAt F S X] :
    Functor.RightDerived.DefinedAt F S (X⟦n⟧) :=
  (objects F S).le_shift n X inferInstance

/-- Source-definedness of a pointwise right-derived value is invariant under every integer
shift. -/
@[stacks 05SC "shift stability of right-derived source-definedness"]
theorem iff_shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    Functor.RightDerived.DefinedAt F S X ↔
      Functor.RightDerived.DefinedAt F S (X⟦n⟧) := sorry

end Functor.RightDerived.DefinedAt

namespace Functor.LeftDerived.DefinedAt

namespace objects

/-- The object property where the left-derived indexing diagram is essentially constant is
stable under integer shifts. -/
@[stacks 05SC "shift-stable left-derived essential-constancy domain"]
instance isStableUnderShift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (Functor.LeftDerived.DefinedAt.objects F S) ℤ where
  isStableUnderShiftBy n := ⟨fun X hX ↦ ⟨left_iso
    (Functor.LeftDerived.Value.Shift.diagramIso F S X n)
    (left_reindex (Functor.LeftDerived.Value.Shift.indexEquivalence S X n)
      (left_map hX.isEssentiallyConstant (shiftFunctor D' n)))⟩⟩

end objects

/-- Source-definedness of a pointwise left-derived value transports through an integer shift. -/
@[stacks 05SC "left-derived source-definedness after a shift"]
instance shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [Functor.LeftDerived.DefinedAt F S X] :
    Functor.LeftDerived.DefinedAt F S (X⟦n⟧) :=
  (objects F S).le_shift n X inferInstance

/-- Source-definedness of a pointwise left-derived value is invariant under every integer
shift. -/
@[stacks 05SC "shift stability of left-derived source-definedness"]
theorem iff_shift [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    Functor.LeftDerived.DefinedAt F S X ↔
      Functor.LeftDerived.DefinedAt F S (X⟦n⟧) := sorry

end Functor.LeftDerived.DefinedAt


end CategoryTheory
