/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Thickening
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Over

/-! # Reduction of directed affine thickening colimits -/

public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.AffineReduction

variable {S : Scheme.{u}}

/-- The empty scheme with its unique structure map to the base. -/
private abbrev emptyOver (S : Scheme.{u}) : Over S := Over.mk (Scheme.emptyTo S)

/-- The reduction of a selected affine stage, or the empty scheme for an empty index. -/
private def schemeFor {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) : Over S := by
  classical
  exact Over.reduction (if h : Nonempty Λ then D.obj (Classical.choice h) else emptyOver S)

/-- The empty sieve covers the empty scheme over the base in the fppf topology. -/
private theorem emptyCover :
    (⊥ : Sieve (emptyOver S)) ∈ (Scheme.fppfTopology.over S) (emptyOver S) := by
  rw [CategoryTheory.GrothendieckTopology.mem_over_iff, OrderIso.map_bot]
  change (⊥ : Sieve (∅ : Scheme.{u})) ∈ Scheme.fppfTopology (∅ : Scheme.{u})
  exact Scheme.bot_mem_grothendieckTopology _

/-- The section of a sheaf on the empty scheme obtained by empty-cover amalgamation. -/
private def emptySection (X : (Over S)ᵒᵖ ⥤ Type u)
    (hX : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X) : X.obj (op (emptyOver S)) :=
  ((isSheaf_iff_isSheaf_of_type _ _).mp hX _ emptyCover).amalgamate
    (fun _ _ h ↦ False.elim h) (by intro _ _ _ _ _ _ _ h; exact h.elim)

/-- The selected reduced stage maps into the sheaf through its supplied colimit comparison. -/
private def ιFor {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X)
    (hX : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X) :
    yoneda.obj (schemeFor D) ⟶ X := by
  classical
  unfold schemeFor
  split
  · exact yoneda.map (Over.reductionι _) ≫ c.ι.app _ ≫ η
  · exact yoneda.map (Over.reductionι _) ≫ yonedaEquiv.symm (emptySection X hX)

/-- Reductions of two stages are compared through a common upper stage. -/
private def stageCompare {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i j : Λ) :
    Over.reduction (D.obj i) ⟶ Over.reduction (D.obj j) :=
  let k := (directed_of (· ≤ ·) i j).choose
  let fi := D.map (homOfLE (directed_of (· ≤ ·) i j).choose_spec.1)
  let fj := D.map (homOfLE (directed_of (· ≤ ·) i j).choose_spec.2)
  (@Over.reductionIsoOfThickening S (D.obj i) (D.obj k) fi
      (h.isThickening_map _)).hom ≫
    (@Over.reductionIsoOfThickening S (D.obj j) (D.obj k) fj
      (h.isThickening_map _)).inv

private theorem stageMap_comp {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    {i j k : Λ} (hij : i ≤ j) (hjk : j ≤ k) :
    Over.reductionMap (D.map (homOfLE hij)) ≫
        Over.reductionMap (D.map (homOfLE hjk)) =
      Over.reductionMap (D.map (homOfLE (hij.trans hjk))) := by
  rw [← Over.reductionMap_comp, ← D.map_comp]
  rfl

private theorem isoSpan_postcomp {C : Type*} [Category C] {A B K L M : C}
    (ei : A ≅ L) (ej : B ≅ L) (ek : K ≅ M)
    (a : A ⟶ K) (b : B ⟶ K) (d : L ⟶ M)
    (ha : ei.hom ≫ d = a ≫ ek.hom) (hb : ej.hom ≫ d = b ≫ ek.hom) :
    (ei.hom ≫ ej.inv) ≫ b = a := by
  apply (cancel_mono ek.hom).1
  rw [Category.assoc, Category.assoc, ← hb, ej.inv_hom_id_assoc, ha]

/-- Comparing two reductions commutes with their maps to any common upper stage. -/
private theorem stageCompare_postcomp {Λ : Type u} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i j k : Λ)
    (hik : i ≤ k) (hjk : j ≤ k) :
    stageCompare D h i j ≫ Over.reductionMap (D.map (homOfLE hjk)) =
      Over.reductionMap (D.map (homOfLE hik)) := by
  classical
  let l := (directed_of (· ≤ ·) i j).choose
  have hil : i ≤ l := (directed_of (· ≤ ·) i j).choose_spec.1
  have hjl : j ≤ l := (directed_of (· ≤ ·) i j).choose_spec.2
  obtain ⟨m, hlm, hkm⟩ := directed_of (· ≤ ·) l k
  let ei := @Over.reductionIsoOfThickening S _ _ (D.map (homOfLE hil))
    (h.isThickening_map _)
  let ej := @Over.reductionIsoOfThickening S _ _ (D.map (homOfLE hjl))
    (h.isThickening_map _)
  let ek := @Over.reductionIsoOfThickening S _ _ (D.map (homOfLE hkm))
    (h.isThickening_map _)
  change (ei.hom ≫ ej.inv) ≫ Over.reductionMap (D.map (homOfLE hjk)) =
    Over.reductionMap (D.map (homOfLE hik))
  apply isoSpan_postcomp ei ej ek _ _ (Over.reductionMap (D.map (homOfLE hlm)))
  · change Over.reductionMap _ ≫ Over.reductionMap _ =
      Over.reductionMap _ ≫ Over.reductionMap _
    rw [stageMap_comp, stageMap_comp]
  · change Over.reductionMap _ ≫ Over.reductionMap _ =
      Over.reductionMap _ ≫ Over.reductionMap _
    rw [stageMap_comp, stageMap_comp]

/-- Comparison of reduced stages is compatible with composition. -/
private theorem stageCompare_comp {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i j k : Λ) :
    stageCompare D h i j ≫ stageCompare D h j k = stageCompare D h i k := by
  obtain ⟨l, hil, hjl⟩ := directed_of (· ≤ ·) i j
  obtain ⟨m, hlm, hkm⟩ := directed_of (· ≤ ·) l k
  let e := @Over.reductionIsoOfThickening S _ _ (D.map (homOfLE hkm))
    (h.isThickening_map _)
  apply (cancel_mono e.hom).1
  change (stageCompare D h i j ≫ stageCompare D h j k) ≫
      Over.reductionMap (D.map (homOfLE hkm)) =
    stageCompare D h i k ≫ Over.reductionMap (D.map (homOfLE hkm))
  rw [Category.assoc, stageCompare_postcomp D h j k m (hjl.trans hlm) hkm,
    stageCompare_postcomp D h i j m (hil.trans hlm) (hjl.trans hlm),
    stageCompare_postcomp D h i k m (hil.trans hlm) hkm]

/-- A reduced transition respects every cocone of the original stages. -/
private theorem stageMap_cocone {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    (c : Cocone (D ⋙ yoneda)) {i j : Λ} (t : i ⟶ j) :
    yoneda.map (Over.reductionMap (D.map t)) ≫
        yoneda.map (Over.reductionι (D.obj j)) ≫ c.ι.app j =
      yoneda.map (Over.reductionι (D.obj i)) ≫ c.ι.app i := by
  have w : Over.reductionMap (D.map t) ≫ Over.reductionι (D.obj j) =
      Over.reductionι (D.obj i) ≫ D.map t := Over.reductionι_naturality (D.map t)
  have hw : yoneda.map (D.map t) ≫ c.ι.app j = c.ι.app i := c.w t
  rw [← Category.assoc, ← yoneda.map_comp, w, yoneda.map_comp,
    Category.assoc, hw]
  rfl

/-- Comparing reduced stages respects their maps into the original colimit. -/
private theorem stageCompare_cocone {Λ : Type u} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (c : Cocone (D ⋙ yoneda)) (i j : Λ) :
    yoneda.map (stageCompare D h i j) ≫
        yoneda.map (Over.reductionι (D.obj j)) ≫ c.ι.app j =
      yoneda.map (Over.reductionι (D.obj i)) ≫ c.ι.app i := by
  let k := (directed_of (· ≤ ·) i j).choose
  have hik : i ≤ k := (directed_of (· ≤ ·) i j).choose_spec.1
  have hjk : j ≤ k := (directed_of (· ≤ ·) i j).choose_spec.2
  let ei := @Over.reductionIsoOfThickening S _ _ (D.map (homOfLE hik))
    (h.isThickening_map _)
  let ej := @Over.reductionIsoOfThickening S _ _ (D.map (homOfLE hjk))
    (h.isThickening_map _)
  have hj : yoneda.map ej.inv ≫ yoneda.map (Over.reductionι (D.obj j)) ≫ c.ι.app j =
      yoneda.map (Over.reductionι (D.obj k)) ≫ c.ι.app k := by
    rw [← stageMap_cocone D c (homOfLE hjk)]
    change yoneda.map ej.inv ≫ yoneda.map ej.hom ≫ _ = _
    rw [← Category.assoc (yoneda.map ej.inv), ← yoneda.map_comp,
      ej.inv_hom_id, yoneda.map_id, Category.id_comp]
  change yoneda.map (ei.hom ≫ ej.inv) ≫ _ = _
  rw [yoneda.map_comp, Category.assoc, hj]
  exact stageMap_cocone D c (homOfLE hik)

/-- A stage maps injectively to the presheaf colimit, since all transitions are monic. -/
private theorem stage_injective {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (c : Cocone (D ⋙ yoneda))
    (hc : IsColimit c) (i : Λ) (T : (Over S)ᵒᵖ) :
    Function.Injective ((c.ι.app i).app T) := by
  intro a b hab
  obtain ⟨j, t, u, heq⟩ := (Types.FilteredColimit.isColimit_eq_iff _
    (isColimitOfPreserves ((evaluation _ _).obj T) hc)).mp hab
  have htu : t = u := Subsingleton.elim _ _
  subst u
  haveI := h.isThickening_map t
  haveI : Mono (D.map t) := Over.mono_of_mono_left _
  apply (cancel_mono (D.map t)).1
  exact heq

/-- Local injectivity of the comparison is injectivity on each representable stage. -/
private theorem stageToX_injective {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (c : Cocone (D ⋙ yoneda))
    (hc : IsColimit c) (η : c.pt ⟶ X)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (i : Λ) (T : (Over S)ᵒᵖ) : Function.Injective (((c.ι.app i) ≫ η).app T) := by
  intro a b hab
  apply ((GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology.over S) (yoneda.obj (D.obj i))) _
    (hη.equalizerSieve_mem ((c.ι.app i).app T a) ((c.ι.app i).app T b) hab)).isSeparatedFor.ext
  intro V g hg
  apply stage_injective D h c hc i (op V)
  change c.pt.map g.op ((c.ι.app i).app T a) =
    c.pt.map g.op ((c.ι.app i).app T b) at hg
  exact (NatTrans.naturality_apply (c.ι.app i) g.op a).trans
    (hg.trans (NatTrans.naturality_apply (c.ι.app i) g.op b).symm)

private theorem reductionι_mono (U : Over S) : Mono (Over.reductionι U) := by
  letI : Mono (Over.reductionι U).left := by
    change Mono (Scheme.reductionι U.left)
    infer_instance
  exact Over.mono_of_mono_left _

private theorem casesOn_pos {p : Prop} {α : Sort*} (d : Decidable p)
    (f : ¬ p → α) (g : p → α) (hp : p) : Decidable.rec f g d = g hp := by
  cases d with
  | isTrue h => rfl
  | isFalse h => exact (h hp).elim

private theorem mpr_heq {α β : Sort u} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by
  cases h
  rfl

/-- The branch computation is heterogeneous because the selected scheme is dependent. -/
private theorem ιFor_heq {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ X)
    (hX : Presheaf.IsSheaf (Scheme.fppfTopology.over S) X) (hn : Nonempty Λ) :
    HEq (ιFor D c η hX)
      (yoneda.map (Over.reductionι (D.obj (Classical.choice hn))) ≫
        c.ι.app (Classical.choice hn) ≫ η) := by
  unfold ιFor
  dsimp only [id]
  erw [casesOn_pos (hp := hn)]
  exact mpr_heq _ _

private theorem injective_app_of_heq {P Q X : (Over S)ᵒᵖ ⥤ Type u}
    {f : P ⟶ X} {g : Q ⟶ X} (hPQ : P = Q) (hfg : HEq f g) (T : (Over S)ᵒᵖ)
    (hg : Function.Injective (g.app T)) : Function.Injective (f.app T) := by
  cases hPQ
  cases (eq_of_heq hfg)
  exact hg

/-- The selected reduction inclusion is injective on sections, including the empty case. -/
private theorem ιFor_injective {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (c : Cocone (D ⋙ yoneda))
    (hc : IsColimit c) (η : c.pt ⟶ X)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (T : (Over S)ᵒᵖ) : Function.Injective ((ιFor D c η h.isSheaf).app T) := by
  classical
  by_cases hn : Nonempty Λ
  · have hs : schemeFor D = Over.reduction (D.obj (Classical.choice hn)) := by
      simp only [schemeFor, dif_pos hn]
    apply injective_app_of_heq (congrArg yoneda.obj hs) (ιFor_heq D c η h.isSheaf hn) T
    intro a b hab
    haveI : Mono (Over.reductionι (D.obj (Classical.choice hn))) :=
      reductionι_mono _
    apply (cancel_mono (Over.reductionι (D.obj (Classical.choice hn)))).1
    exact stageToX_injective D h c hc η hη _ T hab
  · have hs : schemeFor D = Over.reduction (emptyOver S) := by
      simp only [schemeFor, dif_neg hn]
    have hsub : Subsingleton ((yoneda.obj (schemeFor D)).obj T) := by
      rw [hs]
      refine ⟨fun a b ↦ ?_⟩
      haveI : Mono (Over.reductionι (emptyOver S)) := reductionι_mono _
      apply (cancel_mono (Over.reductionι (emptyOver S))).1
      apply Over.OverMorphism.ext
      apply (cancel_mono (Scheme.emptyTo S)).1
      exact (a ≫ Over.reductionι (emptyOver S)).w.trans
        (b ≫ Over.reductionι (emptyOver S)).w.symm
    exact fun a b _ ↦ hsub.elim a b

/-- An element of the presheaf colimit is represented by an actual stage section. -/
private def representative {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) {T : Over S}
    (x : c.pt.obj (op T)) : Σ i, T ⟶ D.obj i :=
  let h := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op T)) hc) x
  ⟨h.choose, h.choose_spec.choose⟩

/-- The chosen representative maps to the original colimit section. -/
private theorem representative_spec {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) {T : Over S}
    (x : c.pt.obj (op T)) :
    (c.ι.app (representative D c hc x).1).app (op T)
      (representative D c hc x).2 = x :=
  (Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves ((evaluation _ _).obj (op T)) hc) x).choose_spec.choose_spec

/-- A stage representative of a section coming from a reduced algebraic space kills the
stage nilradical. -/
private theorem stageFactor_nilradical_le_ker
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T))
    (i : Λ) (a : T ⟶ D.obj i)
    (ha : η.app (op T) ((c.ι.app i).app (op T) a) = f.app (op T) x) :
    (D.obj i).left.nilradical ≤ a.left.ker := sorry

/-- A reduced-stage section is transported to the selected reduced stage. -/
private def toSelectedStage {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i : Λ) :
    Over.reduction (D.obj i) ⟶ schemeFor D := by
  classical
  unfold schemeFor
  split
  · exact stageCompare D h i _
  · exact False.elim (‹¬ Nonempty Λ› ⟨i⟩)

/-- The nonempty branch of stage transport, with its dependent target retained. -/
private theorem toSelectedStage_heq {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (i : Λ) (hn : Nonempty Λ) :
    HEq (toSelectedStage D h i) (stageCompare D h i (Classical.choice hn)) := by
  unfold toSelectedStage
  dsimp only [id]
  erw [casesOn_pos (hp := hn)]
  exact mpr_heq _ _

private theorem yoneda_comp_eq_of_heq {A B B' : Over S} {X : (Over S)ᵒᵖ ⥤ Type u}
    (f : A ⟶ B) (g : yoneda.obj B ⟶ X) (f' : A ⟶ B') (g' : yoneda.obj B' ⟶ X)
    (hB : B = B') (hf : HEq f f') (hg : HEq g g') :
    yoneda.map f ≫ g = yoneda.map f' ≫ g' := by
  cases hB
  cases (eq_of_heq hf)
  cases (eq_of_heq hg)
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Transport to the selected stage preserves the map to the presented sheaf. -/
private theorem toSelectedStage_fac {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) (c : Cocone (D ⋙ yoneda))
    (η : c.pt ⟶ X) (i : Λ) :
    yoneda.map (toSelectedStage D h i) ≫ ιFor D c η h.isSheaf =
      yoneda.map (Over.reductionι (D.obj i)) ≫ c.ι.app i ≫ η := by
  classical
  have hn : Nonempty Λ := ⟨i⟩
  have hs : schemeFor D = Over.reduction (D.obj (Classical.choice hn)) := by
    simp only [schemeFor, dif_pos hn]
  rw [yoneda_comp_eq_of_heq _ _ _ _ hs (toSelectedStage_heq D h i hn)
    (ιFor_heq D c η h.isSheaf hn)]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ η) (stageCompare_cocone D h c i (Classical.choice hn))

/-- Local colimit preimages give concrete sections of the selected reduced stage. -/
private def localFamily {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T)) :
    Presieve.FamilyOfElements (yoneda.obj (schemeFor D))
      (Presheaf.imageSieve η (f.app (op T) x)).arrows := fun V g hg ↦
  let y := Presheaf.localPreimage η (f.app (op T) x) g hg
  let a := representative D c hc y
  let ha : η.app (op V) ((c.ι.app a.1).app (op V) a.2) =
      f.app (op V) (G.functorOfPoints.map g.op x) := by
    rw [representative_spec, Presheaf.app_localPreimage]
    exact (NatTrans.naturality_apply f g.op x).symm
  let hk := stageFactor_nilradical_le_ker D h c hc η hηsurj hη G hG f
    (G.functorOfPoints.map g.op x) a.1 a.2 ha
  let b : V ⟶ Over.reduction (D.obj a.1) :=
    Over.homMk ((D.obj a.1).left.nilradical.lift a.2.left hk) (by
      change (D.obj a.1).left.nilradical.lift a.2.left hk ≫
        ((D.obj a.1).left.nilradical.subschemeι ≫ (D.obj a.1).hom) = V.hom
      rw [← Category.assoc, Scheme.IdealSheafData.lift_subschemeι]
      exact a.2.w)
  b ≫ toSelectedStage D h a.1

/-- Each member of the local family maps to the prescribed section of the sheaf. -/
private theorem localFamily_fac
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T V : Over S} (x : G.functorOfPoints.obj (op T))
    (g : V ⟶ T) (hg : Presheaf.imageSieve η (f.app (op T) x) g) :
    (ιFor D c η h.isSheaf).app (op V)
        (localFamily D h c hc η hηsurj hη G hG f x g hg) =
      f.app (op V) (G.functorOfPoints.map g.op x) := by
  let y := Presheaf.localPreimage η (f.app (op T) x) g hg
  let a := representative D c hc y
  have ha : η.app (op V) ((c.ι.app a.1).app (op V) a.2) =
      f.app (op V) (G.functorOfPoints.map g.op x) := by
    rw [representative_spec, Presheaf.app_localPreimage]
    exact (NatTrans.naturality_apply f g.op x).symm
  let hk := stageFactor_nilradical_le_ker D h c hc η hηsurj hη G hG f
    (G.functorOfPoints.map g.op x) a.1 a.2 ha
  let b : V ⟶ Over.reduction (D.obj a.1) :=
    Over.homMk ((D.obj a.1).left.nilradical.lift a.2.left hk) (by
      change (D.obj a.1).left.nilradical.lift a.2.left hk ≫
        ((D.obj a.1).left.nilradical.subschemeι ≫ (D.obj a.1).hom) = V.hom
      rw [← Category.assoc, Scheme.IdealSheafData.lift_subschemeι]
      exact a.2.w)
  have hb : b ≫ Over.reductionι (D.obj a.1) = a.2 := by
    apply Over.OverMorphism.ext
    exact Scheme.IdealSheafData.lift_subschemeι (D.obj a.1).left.nilradical a.2.left hk
  have ht := congrArg (fun t ↦ t.app (op V) b) (toSelectedStage_fac D h c η a.1)
  change (ιFor D c η h.isSheaf).app (op V) (b ≫ toSelectedStage D h a.1) = _
  change (ιFor D c η h.isSheaf).app (op V) (b ≫ toSelectedStage D h a.1) =
    η.app (op V) ((c.ι.app a.1).app (op V) (b ≫ Over.reductionι (D.obj a.1))) at ht
  rw [ht, hb]
  exact ha

/-- The local reduced-stage sections agree on overlaps. -/
private theorem localFamily_compatible
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hη : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T)) :
    (localFamily D h c hc η hηsurj hη G hG f x).Compatible := by
  intro V W Z g₁ g₂ f₁ f₂ h₁ h₂ heq
  apply ιFor_injective D h c hc η hη (op Z)
  simp only [NatTrans.naturality_apply, localFamily_fac]
  simp only [← comp_apply, Category.assoc, ← Functor.map_comp, ← op_comp, heq]

/-- The lift on sections amalgamates the concrete reduced-stage family. -/
private def liftApp {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T)) :
    T ⟶ schemeFor D :=
  (CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over S) (yoneda.obj (schemeFor D)) _
      (hηsurj.imageSieve_mem (f.app (op T) x))).amalgamate
    (localFamily D h c hc η hηsurj hηinj G hG f x)
    (localFamily_compatible D h c hc η hηsurj hηinj G hG f x)

/-- The amalgamated section maps to the section being lifted. -/
private theorem liftApp_fac
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T : Over S} (x : G.functorOfPoints.obj (op T)) :
    (ιFor D c η h.isSheaf).app (op T) (liftApp D h c hc η hηsurj hηinj G hG f x) =
      f.app (op T) x := by
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp h.isSheaf _
    (hηsurj.imageSieve_mem (f.app (op T) x))).isSeparatedFor.ext
  intro V g hg
  rw [← NatTrans.naturality_apply]
  have hglue : (yoneda.obj (schemeFor D)).map g.op
      (liftApp D h c hc η hηsurj hηinj G hG f x) =
      localFamily D h c hc η hηsurj hηinj G hG f x g hg := by
    exact Presieve.IsSheafFor.valid_glue _ _ g hg
  rw [hglue, localFamily_fac, NatTrans.naturality_apply]

/-- The amalgamated lift commutes with restriction of sections. -/
private theorem lift_naturality
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    {X : (Over S)ᵒᵖ ⥤ Type u} (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) {T V : (Over S)ᵒᵖ} (g : T ⟶ V) :
    G.functorOfPoints.map g ≫
        TypeCat.ofHom (liftApp D h c hc η hηsurj hηinj G hG f) =
      TypeCat.ofHom (liftApp D h c hc η hηsurj hηinj G hG f) ≫
        (yoneda.obj (schemeFor D)).map g := by
  apply ConcreteCategory.hom_ext
  intro x
  apply ιFor_injective D h c hc η hηinj V
  change (ιFor D c η h.isSheaf).app V
      (liftApp D h c hc η hηsurj hηinj G hG f (G.functorOfPoints.map g x)) =
    (ιFor D c η h.isSheaf).app V
      ((yoneda.obj (schemeFor D)).map g (liftApp D h c hc η hηsurj hηinj G hG f x))
  rw [liftApp_fac, NatTrans.naturality_apply (ιFor D c η h.isSheaf), liftApp_fac]
  exact NatTrans.naturality_apply f g x

/-- A map from a reduced algebraic space lifts by the pointwise sheaf-gluing construction. -/
private def liftFor {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : G.functorOfPoints ⟶ yoneda.obj (schemeFor D) where
  app T := TypeCat.ofHom (liftApp D h c hc η hηsurj hηinj G hG f)
  naturality _ _ g := lift_naturality D h c hc η hηsurj hηinj G hG f g

/-- The natural transformation assembled from the sectionwise lifts is a factorization. -/
private theorem liftFor_fac {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (c : Cocone (D ⋙ yoneda)) (hc : IsColimit c) (η : c.pt ⟶ X)
    (hηsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η)
    (hηinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) :
    liftFor D h c hc η hηsurj hηinj G hG f ≫ ιFor D c η h.isSheaf = f := by
  ext T x
  exact liftApp_fac D h c hc η hηsurj hηinj G hG f x

/-- The inclusion uses the cocone and local comparison supplied by the affine presentation. -/
private def ιFromPresentation {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X) : yoneda.obj (schemeFor D) ⟶ X :=
  ιFor D h.exists_colimit.choose h.exists_colimit.choose_spec.choose h.isSheaf

/-- The lift uses the colimit evidence and local comparison supplied by the presentation. -/
private def liftFromPresentation {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ Over S) {X : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsDirectedAffineThickeningColimit D X)
    (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : G.functorOfPoints ⟶ yoneda.obj (schemeFor D) :=
  let c := h.exists_colimit.choose
  let η := h.exists_colimit.choose_spec.choose
  let hc := h.exists_colimit.choose_spec.choose_spec
  liftFor D h c (Classical.choice hc.1) η hc.2.1 hc.2.2 G hG f

variable {X : (Over S)ᵒᵖ ⥤ Type u}
variable (hX : ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
  (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D X)

/-- The index chosen from the supplied affine presentation. -/
private abbrev index : Type u := hX.choose

/-- The order belonging to the chosen presentation index. -/
private abbrev indexOrder : Preorder (index hX) := hX.choose_spec.choose

/-- Directedness belonging to the chosen presentation index. -/
private theorem indexDirected :
    @IsDirected (index hX) (@LE.le (index hX) (indexOrder hX).toLE) :=
  hX.choose_spec.choose_spec.choose

/-- The diagram chosen from the supplied presentation hypothesis. -/
private def diagram :
    @CategoryTheory.Functor (index hX) (@Preorder.smallCategory _ (indexOrder hX))
      (Over S) inferInstance :=
  hX.choose_spec.choose_spec.choose_spec.choose

/-- The chosen diagram retains its supplied affine thickening and colimit properties. -/
private theorem presentation :
    @IsDirectedAffineThickeningColimit S (index hX) (indexOrder hX) (indexDirected hX)
      (diagram hX) X :=
  hX.choose_spec.choose_spec.choose_spec.choose_spec

/-- The reduction of a selected affine stage of a directed affine thickening presentation,
with the empty scheme when the index is empty. -/
def scheme : Over S := @schemeFor S (index hX) (indexOrder hX) (diagram hX)

/-- The inclusion of the selected stage reduction into the affine formal algebraic space. -/
def ι : yoneda.obj (scheme hX) ⟶ X :=
  @ιFromPresentation S (index hX) (indexOrder hX) (indexDirected hX)
    (diagram hX) X (presentation hX)

/-- The selected stage reduction is an affine scheme. -/
theorem scheme_isAffine : IsAffine (scheme hX).left := by
  classical
  unfold scheme schemeFor
  split
  · exact (@IsClosedImmersion.isAffine_surjective_of_isAffine _ _
      ((presentation hX).isAffine_obj _) (Scheme.reductionι _)
      (Scheme.isClosedImmersion_reductionι _)).1
  · exact (@IsClosedImmersion.isAffine_surjective_of_isAffine _ _
      (inferInstance : IsAffine (∅ : Scheme.{u})) (Scheme.reductionι _)
      (Scheme.isClosedImmersion_reductionι _)).1

/-- The selected stage reduction is reduced. -/
theorem scheme_isReduced : IsReduced (scheme hX).left :=
  Scheme.instIsReducedReduction _

/-- Every morphism from a reduced algebraic space into the affine formal algebraic space
has a specified lift to its selected affine reduction. -/
def lift (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : G.functorOfPoints ⟶ yoneda.obj (scheme hX) :=
  @liftFromPresentation S (index hX) (indexOrder hX) (indexDirected hX)
    (diagram hX) X (presentation hX) G hG f

/-- The specified reduction lift followed by the inclusion is the original morphism. -/
theorem lift_fac (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) : lift hX G hG f ≫ ι hX = f := by
  let h := presentation hX
  let c := h.exists_colimit.choose
  let η := h.exists_colimit.choose_spec.choose
  let hc := h.exists_colimit.choose_spec.choose_spec
  exact @liftFor_fac S (index hX) (indexOrder hX) (indexDirected hX)
    (diagram hX) X h c (Classical.choice hc.1) η hc.2.1 hc.2.2 G hG f

/-- Every factorization through the selected affine reduction equals the specified lift. -/
theorem lift_unique (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) (g : G.functorOfPoints ⟶ yoneda.obj (scheme hX))
    (hg : g ≫ ι hX = f) : g = lift hX G hG f := by
  let h := presentation hX
  let c := h.exists_colimit.choose
  let η := h.exists_colimit.choose_spec.choose
  let hc := h.exists_colimit.choose_spec.choose_spec
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro x
  apply @ιFor_injective S (index hX) (indexOrder hX) (indexDirected hX)
    (diagram hX) X h c (Classical.choice hc.1) η hc.2.2 T
  change (g ≫ ι hX).app T x = (lift hX G hG f ≫ ι hX).app T x
  rw [hg, lift_fac]

/-- The specified affine reduction lift satisfies factorization and uniqueness together. -/
theorem spec (G : AlgebraicSpace S)
    (hG : AlgebraicSpace.existsSurjectiveEtale (IsReduced : ObjectProperty Scheme.{u}) G)
    (f : G.functorOfPoints ⟶ X) :
    lift hX G hG f ≫ ι hX = f ∧
      ∀ g : G.functorOfPoints ⟶ yoneda.obj (scheme hX),
        g ≫ ι hX = f → g = lift hX G hG f :=
  ⟨lift_fac hX G hG f, fun g hg ↦ lift_unique hX G hG f g hg⟩

end AlgebraicGeometry.FormalAlgebraicSpace.AffineReduction
