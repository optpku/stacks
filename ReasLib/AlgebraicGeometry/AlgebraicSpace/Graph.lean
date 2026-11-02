/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PullbackComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Diagonal
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Graph

/-!
# Geometric properties of graph morphisms

The graph of a morphism of algebraic spaces over a common base is representable,
locally of finite type, locally quasi-finite, separated, and a monomorphism.
Separation properties of the target over the base imply immersion and
quasi-compactness properties of the graph.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

private theorem graph_diagonal_isPullback {S : Scheme.{u}}
    {X Y T : (Over S)ᵒᵖ ⥤ Type u} (x : X ⟶ T) (y : Y ⟶ T)
    (g : X ⟶ Y) (hg : g ≫ y = x) :
    IsPullback g (pullback.graph x y g hg) (pullback.diagonal y)
      (pullback.graphBaseChangeMap x y g hg) := by
  have hfst : pullback.graph x y g hg ≫ pullback.fst x y = 𝟙 X := by
    unfold pullback.graph
    exact pullback.lift_fst _ _ _
  have hsnd : pullback.graph x y g hg ≫ pullback.snd x y = g := by
    unfold pullback.graph
    exact pullback.lift_snd _ _ _
  have hmapfst : pullback.graphBaseChangeMap x y g hg ≫ pullback.fst y y =
      pullback.fst x y ≫ g :=
    pullback.lift_fst _ _ _
  have hmapsnd : pullback.graphBaseChangeMap x y g hg ≫ pullback.snd y y =
      pullback.snd x y :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by
      change g ≫ pullback.diagonal y =
        pullback.graph x y g hg ≫ pullback.graphBaseChangeMap x y g hg
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, hmapfst, Category.comp_id]
        rw [← Category.assoc, hfst, Category.id_comp]
      · simp only [Category.assoc, pullback.diagonal_snd, hmapsnd, hsnd, Category.comp_id])
    (fun c ↦ c.snd ≫ pullback.fst x y) ?_ ?_ ?_)
  · intro c
    have h := congrArg (fun k ↦ k ≫ pullback.fst y y) c.condition
    simpa only [Category.assoc, pullback.diagonal_fst, hmapfst, Category.comp_id]
      using h.symm
  · intro c
    change (c.snd ≫ pullback.fst x y) ≫ pullback.graph x y g hg = c.snd
    apply pullback.hom_ext
    · simp only [Category.assoc, hfst, Category.comp_id]
    · have h₁ := congrArg (fun k ↦ k ≫ pullback.fst y y) c.condition
      have h₂ := congrArg (fun k ↦ k ≫ pullback.snd y y) c.condition
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
        hmapfst, hmapsnd, Category.comp_id] at h₁ h₂
      simpa only [Category.assoc, hsnd] using h₁.symm.trans h₂
  · intro c m _ hm
    have h := congrArg (fun k ↦ k ≫ pullback.fst x y) hm
    change (m ≫ pullback.graph x y g hg) ≫ pullback.fst x y = _ at h
    simpa only [Category.assoc, hfst, Category.comp_id] using h

-- Compare the chosen algebraic-space pullback with the presheaf pullback before
-- applying base-change stability. The comparison comes from their universal properties.
private theorem graph_presheaf_of_diagonal {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x)
    {P : MorphismProperty (Over S)}
    (h : P.presheaf (pullback.diagonal (C := (Over S)ᵒᵖ ⥤ Type u) y)) :
    P.presheaf (pullback.graph x y g hg) := by
  let sq := ReasLibPullback.isPullback x y
  let e : (pullback x y).functorOfPoints ≅
      pullback (C := (Over S)ᵒᵖ ⥤ Type u) x y :=
    { hom := sq.isoPullback.inv
      inv := sq.isoPullback.hom
      hom_inv_id := sq.isoPullback.inv_hom_id
      inv_hom_id := sq.isoPullback.hom_inv_id }
  letI : IsIso e.hom := e.isIso_hom
  have hfst : e.hom ≫ pullback.fst (C := (Over S)ᵒᵖ ⥤ Type u) x y =
      (pullback.fst x y : pullback x y ⟶ X) :=
    sq.isoPullback_inv_fst
  have hsnd : e.hom ≫ pullback.snd (C := (Over S)ᵒᵖ ⥤ Type u) x y =
      (pullback.snd x y : pullback x y ⟶ Y) :=
    sq.isoPullback_inv_snd
  let d : X.functorOfPoints ⟶ (pullback x y).functorOfPoints :=
    pullback.graph x y g hg
  have hd : d ≫ e.hom =
      pullback.graph (C := (Over S)ᵒᵖ ⥤ Type u) x y g hg := by
    apply pullback.hom_ext
    · rw [Category.assoc, hfst]
      exact (pullback.lift_fst (C := AlgebraicSpace S) (f := x) (g := y)
        (𝟙 X) g ((Category.id_comp x).trans hg.symm)).trans
        (pullback.lift_fst (C := (Over S)ᵒᵖ ⥤ Type u) (f := x) (g := y)
          (𝟙 X.functorOfPoints) g ((Category.id_comp x).trans hg.symm)).symm
    · rw [Category.assoc, hsnd]
      exact (pullback.lift_snd (C := AlgebraicSpace S) (f := x) (g := y)
        (𝟙 X) g ((Category.id_comp x).trans hg.symm)).trans
        (pullback.lift_snd (C := (Over S)ᵒᵖ ⥤ Type u) (f := x) (g := y)
          (𝟙 X.functorOfPoints) g ((Category.id_comp x).trans hg.symm)).symm
  change P.presheaf d
  apply (MorphismProperty.cancel_right_of_respectsIso P.presheaf d e.hom).mp
  rw [hd]
  letI := MorphismProperty.relative_isStableUnderBaseChange P (F := yoneda)
  exact MorphismProperty.of_isPullback (graph_diagonal_isPullback x y g hg) h

/-- The graph of a morphism of algebraic spaces over a common base is representable. -/
theorem relativelyRepresentable_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    yoneda.relativelyRepresentable (pullback.graph x y g hg) := by
  exact (graph_presheaf_of_diagonal x y g hg (P := ⊤)
    ⟨relativelyRepresentable_diagonal y, by intros; trivial⟩).rep

/-- The graph of a morphism of algebraic spaces over a common base is representably
locally of finite type. -/
theorem locallyOfFiniteType_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) := by
  exact graph_presheaf_of_diagonal x y g hg (locallyOfFiniteType_diagonal y)

/-- The graph of a morphism of algebraic spaces over a common base is representably
locally of finite type and locally quasi-finite. -/
theorem locallyQuasiFinite_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.LocallyOfFiniteType ⊓
      @AlgebraicGeometry.LocallyQuasiFinite : MorphismProperty Scheme.{u})).presheaf
      (pullback.graph x y g hg) := by
  exact graph_presheaf_of_diagonal x y g hg (locallyQuasiFinite_diagonal y)

/-- The graph of a morphism of algebraic spaces over a common base is representably
separated. -/
theorem isSeparated_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) := by
  exact graph_presheaf_of_diagonal x y g hg (isSeparated_diagonal y)

/-- The graph of a morphism of algebraic spaces over a common base is a representable
monomorphism. -/
theorem monomorphisms_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) :
    (MorphismProperty.over (MorphismProperty.monomorphisms Scheme.{u})).presheaf
      (pullback.graph x y g hg) := by
  exact graph_presheaf_of_diagonal x y g hg (monomorphisms_diagonal y)

/-- The graph of a morphism of algebraic spaces whose target is locally separated
over the base is an immersion. -/
instance isImmersion_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [LocallySeparated y] :
    IsImmersion (pullback.graph x y g hg) := by
  exact ⟨graph_presheaf_of_diagonal x y g hg
    (inferInstance : LocallySeparated y).isImmersion_diagonal⟩

/-- The graph of a morphism of algebraic spaces whose target is separated over the
base is a closed immersion. -/
instance isClosedImmersion_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [Separated y] :
    IsClosedImmersion (pullback.graph x y g hg) := by
  exact ⟨graph_presheaf_of_diagonal x y g hg
    (inferInstance : Separated y).isClosedImmersion_diagonal⟩

/-- The graph of a morphism of algebraic spaces whose target is quasi-separated
over the base is representably quasi-compact. -/
theorem quasiCompact_graph {S : Scheme.{u}} {X Y T : AlgebraicSpace S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y = x) [QuasiSeparated y] :
    (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact :
        MorphismProperty Scheme.{u})).presheaf (pullback.graph x y g hg) := by
  exact graph_presheaf_of_diagonal x y g hg
    (inferInstance : QuasiSeparated y).quasiCompact_diagonal

end AlgebraicGeometry.AlgebraicSpace
