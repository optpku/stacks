/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Final
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram

/-!
# Transport of essentially constant presentations

This file records the functoriality of presentation-wise essential constancy.  The APIs are
attached to the cone, cocone, or diagram predicate they preserve, rather than to a particular
chapter application.  In particular, they centralize transport across diagram and vertex
isomorphisms, equivalences of indexing categories, and final or initial extension.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits

universe uI vI uJ vJ uC vC

namespace CategoryTheory

namespace Limits.Cocone.IsEssentiallyConstant

/-- Transport an essentially constant cocone presentation across an isomorphism of diagrams. -/
theorem precomposeIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} {c : Cocone M} (hc : c.IsEssentiallyConstant) (e : M ≅ N) :
    ((Cocone.precompose e.inv).obj c).IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨i, { section_ := σ.section_ ≫ e.hom.app i, id := ?_ }, ?_⟩
  · change (σ.section_ ≫ e.hom.app i) ≫ (e.inv.app i ≫ c.ι.app i) = 𝟙 c.pt
    simp [Category.assoc]
  · intro j
    obtain ⟨k, ik, jk, h⟩ := hσ j
    refine ⟨k, ik, jk, ?_⟩
    change N.map jk = (e.inv.app j ≫ c.ι.app j) ≫
      (σ.section_ ≫ e.hom.app i) ≫ N.map ik
    calc
      N.map jk = e.inv.app j ≫ M.map jk ≫ e.hom.app k := by
        rw [e.hom.naturality, e.inv_hom_id_app_assoc]
      _ = e.inv.app j ≫ (c.ι.app j ≫ σ.section_ ≫ M.map ik) ≫ e.hom.app k := by
        rw [h]
      _ = (e.inv.app j ≫ c.ι.app j) ≫ (σ.section_ ≫ e.hom.app i) ≫ N.map ik := by
        simp [Category.assoc, e.hom.naturality]

/-- Transport an essentially constant cocone presentation across an isomorphism of vertices. -/
theorem extendIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c : Cocone M} (hc : c.IsEssentiallyConstant) {X : C} (e : c.pt ≅ X) :
    (c.extend e.hom).IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨i, { section_ := e.inv ≫ σ.section_, id := ?_ }, ?_⟩
  · change (e.inv ≫ σ.section_) ≫ (c.ι.app i ≫ e.hom) = 𝟙 X
    simp [Category.assoc]
  · intro j
    obtain ⟨k, ik, jk, h⟩ := hσ j
    exact ⟨k, ik, jk, by simpa [Cocone.extend, Category.assoc] using h⟩

/-- Transport an essentially constant cocone presentation across an isomorphism of cocones. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cocone M} (hc : c.IsEssentiallyConstant) (e : c ≅ c') :
    c'.IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨i, { section_ := e.inv.hom ≫ σ.section_, id := ?_ }, ?_⟩
  · change (e.inv.hom ≫ σ.section_) ≫ c'.ι.app i = 𝟙 c'.pt
    rw [← e.hom.w i]
    simp only [Category.assoc, σ.id_assoc]
    exact congrArg CoconeMorphism.hom e.inv_hom_id
  · intro j
    obtain ⟨k, ik, jk, h⟩ := hσ j
    refine ⟨k, ik, jk, ?_⟩
    simpa only [← Category.assoc, e.inv.w] using h

/-- Essential constancy of cocone presentations is invariant under isomorphism of cocones. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cocone M} (e : c ≅ c') :
    c.IsEssentiallyConstant ↔ c'.IsEssentiallyConstant :=
  ⟨fun hc ↦ hc.ofIso e, fun hc ↦ hc.ofIso e.symm⟩

/-- Extend an essentially constant cocone presentation along a final functor. -/
theorem extendFinal {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsFiltered I] (H : I ⥤ J) [H.Final] {M : J ⥤ C} {c : Cocone (H ⋙ M)}
    (hc : c.IsEssentiallyConstant) :
    ((Functor.Final.extendCocone).obj c).IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨H.obj i, { section_ := σ.section_, id := ?_ }, ?_⟩
  · change σ.section_ ≫ (Functor.Final.extendCocone.obj c).ι.app (H.obj i) = 𝟙 c.pt
    rw [Functor.Final.extendCocone_obj_ι_app' c (𝟙 (H.obj i))]
    simpa using σ.id
  · intro j
    obtain ⟨k, ik, jk, h⟩ := hσ (Functor.Final.lift H j)
    refine ⟨H.obj k, H.map ik, Functor.Final.homToLift H j ≫ H.map jk, ?_⟩
    change M.map (Functor.Final.homToLift H j ≫ H.map jk) =
      (Functor.Final.extendCocone.obj c).ι.app j ≫ σ.section_ ≫ M.map (H.map ik)
    rw [Functor.Final.extendCocone_obj_ι_app' c (Functor.Final.homToLift H j)]
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ M.map (Functor.Final.homToLift H j) ≫ f) h

end Limits.Cocone.IsEssentiallyConstant

namespace Limits.Cone.IsEssentiallyConstant

/-- Transport an essentially constant cone presentation across an isomorphism of diagrams. -/
theorem postcomposeIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} {c : Cone M} (hc : c.IsEssentiallyConstant) (e : M ≅ N) :
    ((Cone.postcompose e.hom).obj c).IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨i, { retraction := e.inv.app i ≫ σ.retraction, id := ?_ }, ?_⟩
  · change (c.π.app i ≫ e.hom.app i) ≫ (e.inv.app i ≫ σ.retraction) = 𝟙 c.pt
    simp [Category.assoc]
  · intro j
    obtain ⟨k, ki, kj, h⟩ := hσ j
    refine ⟨k, ki, kj, ?_⟩
    change N.map kj = N.map ki ≫ (e.inv.app i ≫ σ.retraction) ≫
      (c.π.app j ≫ e.hom.app j)
    calc
      N.map kj = e.inv.app k ≫ M.map kj ≫ e.hom.app j := by
        rw [← e.inv.naturality_assoc]
        simp
      _ = e.inv.app k ≫ (M.map ki ≫ σ.retraction ≫ c.π.app j) ≫ e.hom.app j := by
        rw [h]
      _ = N.map ki ≫ (e.inv.app i ≫ σ.retraction) ≫ (c.π.app j ≫ e.hom.app j) := by
        simp only [Category.assoc]
        rw [← e.inv.naturality_assoc]

/-- Transport an essentially constant cone presentation across an isomorphism of vertices. -/
theorem extendIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c : Cone M} (hc : c.IsEssentiallyConstant) {X : C} (e : c.pt ≅ X) :
    (c.extend e.inv).IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨i, { retraction := σ.retraction ≫ e.hom, id := ?_ }, ?_⟩
  · change (e.inv ≫ c.π.app i) ≫ (σ.retraction ≫ e.hom) = 𝟙 X
    simp [Category.assoc]
  · intro j
    obtain ⟨k, ki, kj, h⟩ := hσ j
    exact ⟨k, ki, kj, by simpa [Cone.extend, Category.assoc] using h⟩

/-- Transport an essentially constant cone presentation across an isomorphism of cones. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cone M} (hc : c.IsEssentiallyConstant) (e : c ≅ c') :
    c'.IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨i, { retraction := σ.retraction ≫ e.hom.hom, id := ?_ }, ?_⟩
  · change c'.π.app i ≫ (σ.retraction ≫ e.hom.hom) = 𝟙 c'.pt
    rw [← e.inv.w i]
    simp only [Category.assoc, σ.id_assoc]
    exact congrArg ConeMorphism.hom e.inv_hom_id
  · intro j
    obtain ⟨k, ki, kj, h⟩ := hσ j
    refine ⟨k, ki, kj, ?_⟩
    simpa only [Category.assoc, e.hom.w] using h

/-- Essential constancy of cone presentations is invariant under isomorphism of cones. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M : I ⥤ C} {c c' : Cone M} (e : c ≅ c') :
    c.IsEssentiallyConstant ↔ c'.IsEssentiallyConstant :=
  ⟨fun hc ↦ hc.ofIso e, fun hc ↦ hc.ofIso e.symm⟩

/-- Extend an essentially constant cone presentation along an initial functor. -/
theorem extendInitial {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    [IsCofiltered I] (H : I ⥤ J) [H.Initial] {M : J ⥤ C} {c : Cone (H ⋙ M)}
    (hc : c.IsEssentiallyConstant) :
    ((Functor.Initial.extendCone).obj c).IsEssentiallyConstant := by
  obtain ⟨i, σ, hσ⟩ := hc
  refine ⟨H.obj i, { retraction := σ.retraction, id := ?_ }, ?_⟩
  · change (Functor.Initial.extendCone.obj c).π.app (H.obj i) ≫ σ.retraction = 𝟙 c.pt
    rw [Functor.Initial.extendCone_obj_π_app' c (𝟙 (H.obj i))]
    simpa using σ.id
  · intro j
    obtain ⟨k, ki, kj, h⟩ := hσ (Functor.Initial.lift H j)
    refine ⟨H.obj k, H.map ki, H.map kj ≫ Functor.Initial.homToLift H j, ?_⟩
    change M.map (H.map kj ≫ Functor.Initial.homToLift H j) =
      M.map (H.map ki) ≫ σ.retraction ≫ (Functor.Initial.extendCone.obj c).π.app j
    rw [Functor.Initial.extendCone_obj_π_app' c (Functor.Initial.homToLift H j)]
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ f ≫ M.map (Functor.Initial.homToLift H j)) h

end Limits.Cone.IsEssentiallyConstant

namespace IsFiltered.IsEssentiallyConstant

/-- Transport essential constancy of a filtered-oriented diagram across an isomorphism. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) (hM : IsFiltered.IsEssentiallyConstant M) :
    IsFiltered.IsEssentiallyConstant N := by
  obtain ⟨c, hc⟩ := hM
  exact ⟨(Cocone.precompose e.inv).obj c, hc.precomposeIso e⟩

/-- Essential constancy of filtered-oriented diagrams is invariant under isomorphism. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) :
    IsFiltered.IsEssentiallyConstant M ↔ IsFiltered.IsEssentiallyConstant N :=
  ⟨ofIso e, ofIso e.symm⟩

/-- Restriction of an essentially constant filtered-oriented diagram along an equivalence remains
essentially constant. -/
theorem whiskerEquivalence {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) {M : I ⥤ C} (hM : IsFiltered.IsEssentiallyConstant M) :
    IsFiltered.IsEssentiallyConstant (e.functor ⋙ M) := by
  obtain ⟨c, i, σ, hσ⟩ := hM
  refine ⟨c.whisker e.functor, e.inverse.obj i,
    { section_ := σ.section_ ≫ M.map (e.counitIso.inv.app i), id := ?_ }, ?_⟩
  · change (σ.section_ ≫ M.map (e.counitIso.inv.app i)) ≫
      c.ι.app (e.functor.obj (e.inverse.obj i)) = 𝟙 c.pt
    simp [Category.assoc]
  · intro j
    obtain ⟨k, ik, jk, h⟩ := hσ (e.functor.obj j)
    refine ⟨e.inverse.obj k,
      e.functor.preimage (e.counitIso.hom.app i ≫ ik ≫ e.counitIso.inv.app k),
      e.functor.preimage (jk ≫ e.counitIso.inv.app k), ?_⟩
    simpa [Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ f ≫ M.map (e.counitIso.inv.app k)) h

/-- Essential constancy of a filtered-oriented diagram is invariant under reindexing by an
equivalence. -/
theorem whiskerEquivalence_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) (M : I ⥤ C) :
    IsFiltered.IsEssentiallyConstant M ↔ IsFiltered.IsEssentiallyConstant (e.functor ⋙ M) := by
  refine ⟨whiskerEquivalence e, fun hM ↦ ?_⟩
  exact ofIso (e.invFunIdAssoc M) (whiskerEquivalence e.symm hM)

/-- Restricting an essentially constant diagram along a final functor from a filtered category
preserves essential constancy. -/
theorem whiskerFinal {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsFiltered I]
    (H : I ⥤ J) [H.Final] {M : J ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant M) :
    IsFiltered.IsEssentiallyConstant (H ⋙ M) := by
  obtain ⟨c, i, σ, hσ⟩ := hM
  let a := Functor.Final.lift H i
  let f : i ⟶ H.obj a := Functor.Final.homToLift H i
  refine ⟨c.whisker H, a, { section_ := σ.section_ ≫ M.map f, id := ?_ }, ?_⟩
  · change (σ.section_ ≫ M.map f) ≫ c.ι.app (H.obj a) = 𝟙 c.pt
    simp [Category.assoc]
  · intro j
    obtain ⟨k, ik, jk, h⟩ := hσ (H.obj j)
    let b := Functor.Final.lift H k
    let g : k ⟶ H.obj b := Functor.Final.homToLift H k
    haveI : IsFiltered (StructuredArrow i H) :=
      (Functor.final_iff_isFiltered_structuredArrow H).mp inferInstance i
    obtain ⟨s, u, v, _⟩ := IsFilteredOrEmpty.cocone_objs
      (StructuredArrow.mk f) (StructuredArrow.mk (ik ≫ g))
    have hi : f ≫ H.map u.right = ik ≫ g ≫ H.map v.right := by
      simpa only [StructuredArrow.mk_hom_eq_self, Category.assoc] using u.w.trans v.w.symm
    haveI : IsFiltered (StructuredArrow (H.obj j) H) :=
      (Functor.final_iff_isFiltered_structuredArrow H).mp inferInstance (H.obj j)
    obtain ⟨t, p, q, _⟩ := IsFilteredOrEmpty.cocone_objs
      (StructuredArrow.mk (𝟙 (H.obj j))) (StructuredArrow.mk (jk ≫ g ≫ H.map v.right))
    have hj : H.map p.right = jk ≫ g ≫ H.map v.right ≫ H.map q.right := by
      simpa only [StructuredArrow.mk_hom_eq_self, Category.id_comp, Category.assoc] using p.w.trans q.w.symm
    refine ⟨t.right, u.right ≫ q.right, p.right, ?_⟩
    change M.map (H.map p.right) = c.ι.app (H.obj j) ≫
      (σ.section_ ≫ M.map f) ≫ M.map (H.map (u.right ≫ q.right))
    calc
      M.map (H.map p.right) = M.map jk ≫
          M.map (g ≫ H.map v.right ≫ H.map q.right) := by
        rw [hj]
        simp [Functor.map_comp]
      _ = c.ι.app (H.obj j) ≫ σ.section_ ≫
          M.map (ik ≫ g ≫ H.map v.right ≫ H.map q.right) := by
        rw [h]
        simp [Functor.map_comp, Category.assoc]
      _ = c.ι.app (H.obj j) ≫ σ.section_ ≫
          M.map ((f ≫ H.map u.right) ≫ H.map q.right) := by
        rw [hi]
        simp [Category.assoc]
      _ = c.ι.app (H.obj j) ≫ (σ.section_ ≫ M.map f) ≫
          M.map (H.map (u.right ≫ q.right)) := by
        simp [Functor.map_comp, Category.assoc]

/-- Essential constancy detected after restriction along a final functor from a filtered
category holds for the original diagram. -/
theorem of_whiskerFinal {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsFiltered I]
    (H : I ⥤ J) [H.Final] {M : J ⥤ C}
    (hM : IsFiltered.IsEssentiallyConstant (H ⋙ M)) :
    IsFiltered.IsEssentiallyConstant M := by
  obtain ⟨c, hc⟩ := hM
  exact ⟨Functor.Final.extendCocone.obj c,
    Limits.Cocone.IsEssentiallyConstant.extendFinal H hc⟩

/-- Essential constancy of a filtered-oriented diagram is detected by restriction along a final
functor from a filtered category. -/
@[stacks 05PV "final reindexing of essentially constant diagrams"]
theorem whiskerFinal_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsFiltered I]
    (H : I ⥤ J) [H.Final] (M : J ⥤ C) :
    IsFiltered.IsEssentiallyConstant M ↔
      IsFiltered.IsEssentiallyConstant (H ⋙ M) :=
  ⟨whiskerFinal H, of_whiskerFinal H⟩

end IsFiltered.IsEssentiallyConstant

namespace IsCofiltered.IsEssentiallyConstant

/-- Transport essential constancy of a cofiltered-oriented diagram across an isomorphism. -/
theorem ofIso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) (hM : IsCofiltered.IsEssentiallyConstant M) :
    IsCofiltered.IsEssentiallyConstant N := by
  obtain ⟨c, hc⟩ := hM
  exact ⟨(Cone.postcompose e.hom).obj c, hc.postcomposeIso e⟩

/-- Essential constancy of cofiltered-oriented diagrams is invariant under isomorphism. -/
theorem iff_of_iso {I : Type uI} {C : Type uC} [Category.{vI} I] [Category.{vC} C]
    {M N : I ⥤ C} (e : M ≅ N) :
    IsCofiltered.IsEssentiallyConstant M ↔ IsCofiltered.IsEssentiallyConstant N :=
  ⟨ofIso e, ofIso e.symm⟩

/-- Restriction of an essentially constant cofiltered-oriented diagram along an equivalence
remains essentially constant. -/
theorem whiskerEquivalence {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) {M : I ⥤ C} (hM : IsCofiltered.IsEssentiallyConstant M) :
    IsCofiltered.IsEssentiallyConstant (e.functor ⋙ M) := by
  obtain ⟨c, i, σ, hσ⟩ := hM
  refine ⟨c.whisker e.functor, e.inverse.obj i,
    { retraction := M.map (e.counitIso.hom.app i) ≫ σ.retraction, id := ?_ }, ?_⟩
  · change c.π.app (e.functor.obj (e.inverse.obj i)) ≫
      (M.map (e.counitIso.hom.app i) ≫ σ.retraction) = 𝟙 c.pt
    simp [← Category.assoc]
  · intro j
    obtain ⟨k, ki, kj, h⟩ := hσ (e.functor.obj j)
    refine ⟨e.inverse.obj k,
      e.functor.preimage (e.counitIso.hom.app k ≫ ki ≫ e.counitIso.inv.app i),
      e.functor.preimage (e.counitIso.hom.app k ≫ kj), ?_⟩
    simpa [Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ M.map (e.counitIso.hom.app k) ≫ f) h

/-- Essential constancy of a cofiltered-oriented diagram is invariant under reindexing by an
equivalence. -/
theorem whiskerEquivalence_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]
    (e : J ≌ I) (M : I ⥤ C) :
    IsCofiltered.IsEssentiallyConstant M ↔
      IsCofiltered.IsEssentiallyConstant (e.functor ⋙ M) := by
  refine ⟨whiskerEquivalence e, fun hM ↦ ?_⟩
  exact ofIso (e.invFunIdAssoc M) (whiskerEquivalence e.symm hM)

/-- Restricting an essentially constant diagram along an initial functor from a cofiltered
category preserves essential constancy. -/
theorem whiskerInitial {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] {M : J ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant M) :
    IsCofiltered.IsEssentiallyConstant (H ⋙ M) := by
  obtain ⟨c, i, σ, hσ⟩ := hM
  let a := Functor.Initial.lift H i
  let f : H.obj a ⟶ i := Functor.Initial.homToLift H i
  refine ⟨c.whisker H, a, { retraction := M.map f ≫ σ.retraction, id := ?_ }, ?_⟩
  · change c.π.app (H.obj a) ≫ (M.map f ≫ σ.retraction) = 𝟙 c.pt
    simp [← Category.assoc]
  · intro j
    obtain ⟨k, ki, kj, h⟩ := hσ (H.obj j)
    let b := Functor.Initial.lift H k
    let g : H.obj b ⟶ k := Functor.Initial.homToLift H k
    haveI : IsCofiltered (CostructuredArrow H i) :=
      (Functor.initial_iff_isCofiltered_costructuredArrow H).mp inferInstance i
    obtain ⟨s, u, v, _⟩ := IsCofilteredOrEmpty.cone_objs
      (CostructuredArrow.mk f) (CostructuredArrow.mk (g ≫ ki))
    have hi : H.map u.left ≫ f = H.map v.left ≫ g ≫ ki := by
      simpa only [CostructuredArrow.mk_hom_eq_self, Category.assoc] using u.w.trans v.w.symm
    haveI : IsCofiltered (CostructuredArrow H (H.obj j)) :=
      (Functor.initial_iff_isCofiltered_costructuredArrow H).mp inferInstance (H.obj j)
    obtain ⟨t, p, q, _⟩ := IsCofilteredOrEmpty.cone_objs
      (CostructuredArrow.mk (𝟙 (H.obj j))) (CostructuredArrow.mk (H.map v.left ≫ g ≫ kj))
    have hj : H.map p.left = H.map q.left ≫ H.map v.left ≫ g ≫ kj := by
      simpa [Category.assoc] using p.w.trans q.w.symm
    refine ⟨t.left, q.left ≫ u.left, p.left, ?_⟩
    change M.map (H.map p.left) = M.map (H.map (q.left ≫ u.left)) ≫
      (M.map f ≫ σ.retraction) ≫ c.π.app (H.obj j)
    calc
      M.map (H.map p.left) = M.map (H.map q.left ≫ H.map v.left ≫ g) ≫ M.map kj := by
        rw [hj]
        simp [Functor.map_comp, Category.assoc]
      _ = M.map (H.map q.left ≫ H.map v.left ≫ g ≫ ki) ≫
          σ.retraction ≫ c.π.app (H.obj j) := by
        rw [h]
        simp [Functor.map_comp, Category.assoc]
      _ = M.map (H.map q.left ≫ (H.map u.left ≫ f)) ≫
          σ.retraction ≫ c.π.app (H.obj j) := by
        rw [hi]
      _ = M.map (H.map (q.left ≫ u.left)) ≫ (M.map f ≫ σ.retraction) ≫
          c.π.app (H.obj j) := by
        simp [Functor.map_comp, Category.assoc]

/-- Essential constancy detected after restriction along an initial functor from a cofiltered
category holds for the original diagram. -/
theorem of_whiskerInitial {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] {M : J ⥤ C}
    (hM : IsCofiltered.IsEssentiallyConstant (H ⋙ M)) :
    IsCofiltered.IsEssentiallyConstant M := by
  obtain ⟨c, hc⟩ := hM
  exact ⟨Functor.Initial.extendCone.obj c,
    Limits.Cone.IsEssentiallyConstant.extendInitial H hc⟩

/-- Essential constancy of a cofiltered-oriented diagram is detected by restriction along an
initial functor from a cofiltered category. -/
@[stacks 05PV "initial reindexing of essentially constant diagrams"]
theorem whiskerInitial_iff {I : Type uI} {J : Type uJ} {C : Type uC}
    [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C] [IsCofiltered I]
    (H : I ⥤ J) [H.Initial] (M : J ⥤ C) :
    IsCofiltered.IsEssentiallyConstant M ↔
      IsCofiltered.IsEssentiallyConstant (H ⋙ M) :=
  ⟨whiskerInitial H, of_whiskerInitial H⟩

end IsCofiltered.IsEssentiallyConstant

end CategoryTheory
