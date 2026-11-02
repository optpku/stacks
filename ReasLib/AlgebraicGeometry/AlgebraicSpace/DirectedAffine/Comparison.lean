/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Atlas

/-!
# Comparison of a presentation quotient with a directed sheaf limit

This module constructs the limiting atlas, relation, coequalizer, and comparison morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

open AlgebraicSpace Atlas

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (i0 : I) (P : Presentation (D.obj (OrderDual.toDual i0)))

/-- A chosen upper bound of two indices in a directed preorder. -/
def directedBound (a b : I) : I :=
  Classical.choose (directed_of (· ≤ ·) a b)

/-- The chosen upper bound is at least its first argument. -/
theorem directedBound_le_left (a b : I) : a ≤ directedBound a b :=
  (Classical.choose_spec (directed_of (· ≤ ·) a b)).1

/-- The chosen upper bound is at least its second argument. -/
theorem directedBound_le_right (a b : I) : b ≤ directedBound a b :=
  (Classical.choose_spec (directed_of (· ≤ ·) a b)).2

/-- The inverse limit of the sheaf-valued algebraic-space diagram. -/
def sheafLimit : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  limit (D ⋙ toSheaf)

/-- The projection from the sheaf limit to a stage. -/
def sheafLimit_π (i : OrderDual I) :
    sheafLimit D ⟶ toSheaf.obj (D.obj i) :=
  limit.π (D ⋙ toSheaf) i

/-- The inverse limit of the stagewise sheaf atlases on the cofinal tail. -/
def limitAtlas : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  limit (Atlas.atlasDiagram D i0 P)

/-- The projection from the limiting atlas to a stage. -/
def limitAtlas_π (i : I) (hi : i0 ≤ i) :
    limitAtlas D i0 P ⟶ Atlas.atlasStage D i0 P i hi :=
  limit.π (Atlas.atlasDiagram D i0 P) (OrderDual.toDual ⟨i, hi⟩)

/-- The composite from the limiting atlas to a stage of the original system. -/
def limitAtlasToStageSheaf (i : I) (hi : i0 ≤ i) :
    limitAtlas D i0 P ⟶ toSheaf.obj (D.obj (OrderDual.toDual i)) :=
  limitAtlas_π D i0 P i hi ≫ Atlas.stageAtlas D i0 P i hi

/-- The relation diagram obtained from the stagewise kernel pairs. -/
def limitRelation : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  limit (Atlas.relationDiagram D i0 P)

/-- The first map from the limiting relation to the limiting atlas. -/
def limitRelationFst :
    limitRelation D i0 P ⟶ limitAtlas D i0 P :=
  limMap (Atlas.relationDiagramFst D i0 P)

/-- The second map from the limiting relation to the limiting atlas. -/
def limitRelationSnd :
    limitRelation D i0 P ⟶ limitAtlas D i0 P :=
  limMap (Atlas.relationDiagramSnd D i0 P)

/-- The coequalizer of the two limiting relation projections. -/
def limitQuotient : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  coequalizer (limitRelationFst D i0 P) (limitRelationSnd D i0 P)

/-- The quotient map from the limiting atlas to its coequalizer. -/
def limitQuotientMap :
    limitAtlas D i0 P ⟶ limitQuotient D i0 P :=
  coequalizer.π (limitRelationFst D i0 P) (limitRelationSnd D i0 P)

/-- The component of the atlas cone at an arbitrary index. -/
def coneFromLimitAtlas_π (j : OrderDual I) :
    limitAtlas D i0 P ⟶ (D ⋙ toSheaf).obj j :=
  limitAtlasToStageSheaf D i0 P (directedBound i0 (OrderDual.ofDual j))
      (directedBound_le_left i0 (OrderDual.ofDual j)) ≫
    toSheaf.map (D.map (homOfLE (directedBound_le_right i0 (OrderDual.ofDual j))))

set_option backward.isDefEq.respectTransparency false in
/-- The maps from the limiting atlas to tail stages commute with transitions. -/
theorem limitAtlasToStageSheaf_naturality {i j : I}
    (hi : i0 ≤ i) (hj : i0 ≤ j) (hij : j ≤ i) :
    limitAtlasToStageSheaf D i0 P i hi ≫ toSheaf.map (D.map (homOfLE hij)) =
      limitAtlasToStageSheaf D i0 P j hj := by
  unfold limitAtlasToStageSheaf
  rw [Category.assoc, ← Atlas.atlasStageHom_fst D i0 P hi hj hij, ← Category.assoc]
  exact congrArg (fun f => f ≫ Atlas.stageAtlas D i0 P j hj)
    (limit.w (Atlas.atlasDiagram D i0 P)
      (homOfLE hij : OrderDual.toDual (⟨i, hi⟩ : Tail i0) ⟶
        OrderDual.toDual (⟨j, hj⟩ : Tail i0)))

set_option backward.isDefEq.respectTransparency false in
/-- Any tail stage above an index computes the corresponding atlas cone component. -/
theorem coneFromLimitAtlas_π_eq (j : OrderDual I) (i : I)
    (hi : i0 ≤ i) (hji : OrderDual.ofDual j ≤ i) :
    coneFromLimitAtlas_π D i0 P j =
      limitAtlasToStageSheaf D i0 P i hi ≫ toSheaf.map (D.map (homOfLE hji)) := by
  let k := directedBound i0 (OrderDual.ofDual j)
  let b := directedBound k i
  have hk : i0 ≤ k := directedBound_le_left _ _
  have hb : i0 ≤ b := le_trans hk (directedBound_le_left k i)
  have h₁ := limitAtlasToStageSheaf_naturality D i0 P hb hk
    (directedBound_le_left k i)
  have h₂ := limitAtlasToStageSheaf_naturality D i0 P hb hi
    (directedBound_le_right k i)
  change limitAtlasToStageSheaf D i0 P k hk ≫ _ = _
  rw [← h₁, ← h₂]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

/-- The tail component of the atlas cone is its stage projection. -/
theorem coneFromLimitAtlas_π_tail (i : Tail i0) :
    coneFromLimitAtlas_π D i0 P (OrderDual.toDual i) =
      limitAtlasToStageSheaf D i0 P i.1 i.2 := by
  exact limitAtlasToStageSheaf_naturality D i0 P
    (directedBound_le_left i0 i.1) i.2 (directedBound_le_right i0 i.1)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the atlas cone components. -/
theorem coneFromLimitAtlas_naturality ⦃j j' : OrderDual I⦄ (f : j ⟶ j') :
    ((Functor.const (OrderDual I)).obj (limitAtlas D i0 P)).map f ≫
        coneFromLimitAtlas_π D i0 P j' =
      coneFromLimitAtlas_π D i0 P j ≫ (D ⋙ toSheaf).map f := by
  change coneFromLimitAtlas_π D i0 P j' =
    coneFromLimitAtlas_π D i0 P j ≫ toSheaf.map (D.map f)
  rw [coneFromLimitAtlas_π_eq D i0 P j'
    (directedBound i0 (OrderDual.ofDual j)) (directedBound_le_left _ _)
    (le_trans (leOfHom f) (directedBound_le_right _ _))]
  dsimp only [coneFromLimitAtlas_π]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

/-- The cone from the limiting atlas to the original sheaf diagram. -/
def coneFromLimitAtlas : Cone (D ⋙ toSheaf) where
  pt := limitAtlas D i0 P
  π :=
    { app := coneFromLimitAtlas_π D i0 P
      naturality := coneFromLimitAtlas_naturality D i0 P }

/-- The canonical map from the limiting atlas to the sheaf limit. -/
def limitAtlasToSheafLimit :
    limitAtlas D i0 P ⟶ sheafLimit D :=
  limit.lift (D ⋙ toSheaf) (coneFromLimitAtlas D i0 P)

set_option backward.isDefEq.respectTransparency false in
/-- The limiting relation is the kernel pair of the canonical atlas map. -/
theorem limitRelation_isKernelPair :
    IsKernelPair (limitAtlasToSheafLimit D i0 P)
      (limitRelationFst D i0 P) (limitRelationSnd D i0 P) := by
  have p₁ (i : OrderDual (Tail i0)) :
      limitRelationFst D i0 P ≫ limitAtlas_π D i0 P i.1 i.2 =
        limit.π (Atlas.relationDiagram D i0 P) i ≫
          Atlas.relationStageFst D i0 P i.1 i.2 :=
    limMap_π (Atlas.relationDiagramFst D i0 P) i
  have p₂ (i : OrderDual (Tail i0)) :
      limitRelationSnd D i0 P ≫ limitAtlas_π D i0 P i.1 i.2 =
        limit.π (Atlas.relationDiagram D i0 P) i ≫
          Atlas.relationStageSnd D i0 P i.1 i.2 :=
    limMap_π (Atlas.relationDiagramSnd D i0 P) i
  have stage_w (i : I) (hi : i0 ≤ i) :
      limitRelationFst D i0 P ≫ limitAtlasToStageSheaf D i0 P i hi =
        limitRelationSnd D i0 P ≫ limitAtlasToStageSheaf D i0 P i hi := by
    unfold limitAtlasToStageSheaf
    rw [← Category.assoc, ← Category.assoc]
    erw [p₁ (OrderDual.toDual ⟨i, hi⟩), p₂ (OrderDual.toDual ⟨i, hi⟩)]
    simp only [Category.assoc, Atlas.relationStageFst, Atlas.relationStageSnd,
      Atlas.stageAtlas, pullback.condition]
  have w : limitRelationFst D i0 P ≫ limitAtlasToSheafLimit D i0 P =
      limitRelationSnd D i0 P ≫ limitAtlasToSheafLimit D i0 P := by
    apply limit.hom_ext
    intro j
    simp only [Category.assoc, limitAtlasToSheafLimit, limit.lift_π]
    change limitRelationFst D i0 P ≫ coneFromLimitAtlas_π D i0 P j =
      limitRelationSnd D i0 P ≫ coneFromLimitAtlas_π D i0 P j
    simpa only [coneFromLimitAtlas_π, Category.assoc] using
      congrArg (fun f => f ≫
        toSheaf.map (D.map (homOfLE (directedBound_le_right i0 (OrderDual.ofDual j)))))
        (stage_w (directedBound i0 (OrderDual.ofDual j)) (directedBound_le_left _ _))
  have stage_condition (s : PullbackCone (limitAtlasToSheafLimit D i0 P)
      (limitAtlasToSheafLimit D i0 P)) (i : OrderDual (Tail i0)) :
      (s.fst ≫ limitAtlas_π D i0 P i.1 i.2) ≫ Atlas.stageAtlas D i0 P i.1 i.2 =
        (s.snd ≫ limitAtlas_π D i0 P i.1 i.2) ≫ Atlas.stageAtlas D i0 P i.1 i.2 := by
    have h := congrArg (fun f => f ≫ sheafLimit_π D (OrderDual.toDual i.1)) s.condition
    simp only [Category.assoc, limitAtlasToSheafLimit, sheafLimit_π, limit.lift_π] at h
    change s.fst ≫ coneFromLimitAtlas_π D i0 P (OrderDual.toDual i.1) =
      s.snd ≫ coneFromLimitAtlas_π D i0 P (OrderDual.toDual i.1) at h
    erw [coneFromLimitAtlas_π_tail D i0 P (⟨i.1, i.2⟩ : Tail i0)] at h
    simpa only [limitAtlasToStageSheaf, Category.assoc] using! h
  let c (s : PullbackCone (limitAtlasToSheafLimit D i0 P)
      (limitAtlasToSheafLimit D i0 P)) : Cone (Atlas.relationDiagram D i0 P) :=
    { pt := s.pt
      π :=
        { app := fun i => pullback.lift (s.fst ≫ limitAtlas_π D i0 P i.1 i.2)
            (s.snd ≫ limitAtlas_π D i0 P i.1 i.2) (stage_condition s i)
          naturality := by
            intro i j f
            change 𝟙 _ ≫ pullback.lift _ _ _ =
              pullback.lift _ _ _ ≫ Atlas.relationStageHom D i0 P i.2 j.2 (leOfHom f)
            apply pullback.hom_ext
            · simp only [Category.id_comp, Category.assoc, Atlas.relationStageHom,
                pullback.lift_fst, pullback.lift_fst_assoc]
              exact (congrArg (fun g => s.fst ≫ g)
                (limit.w (Atlas.atlasDiagram D i0 P) f)).symm
            · simp only [Category.id_comp, Category.assoc, Atlas.relationStageHom,
                pullback.lift_snd, pullback.lift_snd_assoc]
              exact (congrArg (fun g => s.snd ≫ g)
                (limit.w (Atlas.atlasDiagram D i0 P) f)).symm } }
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk w
    (fun s => limit.lift (Atlas.relationDiagram D i0 P) (c s)) ?_ ?_ ?_⟩⟩
  · intro s
    apply limit.hom_ext
    intro i
    change (limit.lift _ (c s) ≫ limitRelationFst D i0 P) ≫
      limitAtlas_π D i0 P i.1 i.2 = s.fst ≫ limitAtlas_π D i0 P i.1 i.2
    rw [Category.assoc, p₁ i, ← Category.assoc, limit.lift_π]
    exact pullback.lift_fst _ _ _
  · intro s
    apply limit.hom_ext
    intro i
    change (limit.lift _ (c s) ≫ limitRelationSnd D i0 P) ≫
      limitAtlas_π D i0 P i.1 i.2 = s.snd ≫ limitAtlas_π D i0 P i.1 i.2
    rw [Category.assoc, p₂ i, ← Category.assoc, limit.lift_π]
    exact pullback.lift_snd _ _ _
  · intro s m hm₁ hm₂
    apply limit.hom_ext
    intro i
    rw [limit.lift_π]
    apply pullback.hom_ext
    · change (m ≫ limit.π (Atlas.relationDiagram D i0 P) i) ≫
        Atlas.relationStageFst D i0 P i.1 i.2 =
          (c s).π.app i ≫ Atlas.relationStageFst D i0 P i.1 i.2
      rw [Category.assoc, ← p₁ i, ← Category.assoc, hm₁]
      exact (pullback.lift_fst _ _ _).symm
    · change (m ≫ limit.π (Atlas.relationDiagram D i0 P) i) ≫
        Atlas.relationStageSnd D i0 P i.1 i.2 =
          (c s).π.app i ≫ Atlas.relationStageSnd D i0 P i.1 i.2
      rw [Category.assoc, ← p₂ i, ← Category.assoc, hm₂]
      exact (pullback.lift_snd _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the limiting atlas to the sheaf limit is an epimorphism. -/
theorem limitAtlasToSheafLimit_epi : Epi (limitAtlasToSheafLimit D i0 P) := by
  let J := Scheme.fppfTopology.over S
  -- A lift to the base atlas gives compatible lifts at every tail stage.
  have lift_exists {T : Sheaf J (Type (u + 1))} (a : T ⟶ sheafLimit D)
      (b : T ⟶ J.uliftYoneda.{u + 1}.obj P.U)
      (w : a ≫ sheafLimit_π D (OrderDual.toDual i0) = b ≫ atlasToSheaf P) :
      ∃ l : T ⟶ limitAtlas D i0 P, l ≫ limitAtlasToSheafLimit D i0 P = a := by
    have stage_condition (i : OrderDual (Tail i0)) :
        (a ≫ sheafLimit_π D (OrderDual.toDual i.1)) ≫
            Atlas.stageTransition D i0 i.1 i.2 = b ≫ atlasToSheaf P := by
      rw [Category.assoc]
      change a ≫ limit.π (D ⋙ toSheaf) (OrderDual.toDual i.1) ≫
        (D ⋙ toSheaf).map (homOfLE i.2) = _
      rw [limit.w]
      exact w
    let c : Cone (Atlas.atlasDiagram D i0 P) :=
      { pt := T
        π :=
          { app := fun i => pullback.lift
              (a ≫ sheafLimit_π D (OrderDual.toDual i.1)) b (stage_condition i)
            naturality := by
              intro i j f
              change 𝟙 _ ≫ pullback.lift _ _ _ =
                pullback.lift _ _ _ ≫ Atlas.atlasStageHom D i0 P i.2 j.2 (leOfHom f)
              apply pullback.hom_ext
              · simp only [Category.id_comp, Category.assoc, Atlas.atlasStageHom, Atlas.stageAtlas,
                  pullback.lift_fst, pullback.lift_fst_assoc]
                exact (congrArg (fun g => a ≫ g)
                  (limit.w (D ⋙ toSheaf)
                    (homOfLE (leOfHom f) : OrderDual.toDual i.1 ⟶
                      OrderDual.toDual j.1))).symm
              · simp only [Category.id_comp, Category.assoc, Atlas.atlasStageHom, Atlas.atlasStage_snd,
                  pullback.lift_snd] } }
    refine ⟨limit.lift (Atlas.atlasDiagram D i0 P) c, ?_⟩
    apply limit.hom_ext
    intro j
    simp only [Category.assoc, limitAtlasToSheafLimit, limit.lift_π]
    change limit.lift (Atlas.atlasDiagram D i0 P) c ≫ coneFromLimitAtlas_π D i0 P j =
      a ≫ sheafLimit_π D j
    dsimp only [coneFromLimitAtlas_π, limitAtlasToStageSheaf, limitAtlas_π]
    rw [← Category.assoc, ← Category.assoc, limit.lift_π]
    change (pullback.lift _ _ _ ≫ Atlas.stageAtlas D i0 P
      (directedBound i0 (OrderDual.ofDual j)) (directedBound_le_left _ _)) ≫ _ = _
    unfold Atlas.stageAtlas
    erw [pullback.lift_fst]
    change (a ≫ limit.π (D ⋙ toSheaf) _) ≫
      (D ⋙ toSheaf).map (homOfLE (directedBound_le_right i0 (OrderDual.ofDual j))) = _
    rw [Category.assoc, limit.w]
    rfl
  -- The base atlas is locally surjective also for the fppf topology and after ULift.
  have h_top : Scheme.etaleTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono
      (Scheme.precoverage_mono fun _ _ _ _ => ⟨inferInstance, inferInstance⟩)
  have h_over : Scheme.etaleTopology.over S ≤ J := by
    intro T R hR
    rw [GrothendieckTopology.mem_over_iff] at hR ⊢
    exact h_top _ hR
  have hs := Presheaf.isLocallySurjective_of_le h_over P.atlas P.atlas_locallySurjective
  have hU : Sheaf.IsLocallySurjective (atlasToSheaf P) := by
    constructor
    intro T s
    apply J.superset_covering _ (hs.imageSieve_mem s.down)
    rintro V g ⟨t, ht⟩
    exact ⟨⟨t⟩, congrArg ULift.up ht⟩
  have hf : Sheaf.IsLocallySurjective (limitAtlasToSheafLimit D i0 P) := by
    constructor
    intro T s
    let x₀ := (sheafLimit_π D (OrderDual.toDual i0)).hom.app (Opposite.op T) s
    apply J.superset_covering _ (hU.imageSieve_mem x₀)
    rintro V g ⟨b, hb⟩
    let a := (GrothendieckTopology.uliftYonedaEquiv.{u + 1} J).symm
      ((sheafLimit D).obj.map g.op s)
    let b' := (GrothendieckTopology.uliftYonedaEquiv.{u + 1} J).symm b
    have w : a ≫ sheafLimit_π D (OrderDual.toDual i0) = b' ≫ atlasToSheaf P := by
      apply (GrothendieckTopology.uliftYonedaEquiv.{u + 1} J).injective
      simp only [GrothendieckTopology.uliftYonedaEquiv_comp, a, b', Equiv.apply_symm_apply]
      exact (NatTrans.naturality_apply
        (sheafLimit_π D (OrderDual.toDual i0)).hom g.op s).trans hb.symm
    obtain ⟨l, hl⟩ := lift_exists a b' w
    refine ⟨GrothendieckTopology.uliftYonedaEquiv.{u + 1} J l, ?_⟩
    simpa only [GrothendieckTopology.uliftYonedaEquiv_comp, a, Equiv.apply_symm_apply]
      using congrArg (GrothendieckTopology.uliftYonedaEquiv.{u + 1} J) hl
  letI := hf
  infer_instance

/-- The canonical atlas map equalizes the two limiting relation projections. -/
theorem limitAtlasToSheafLimit_equalizes :
    limitRelationFst D i0 P ≫ limitAtlasToSheafLimit D i0 P =
      limitRelationSnd D i0 P ≫ limitAtlasToSheafLimit D i0 P :=
  (limitRelation_isKernelPair D i0 P).w

/-- The comparison from the limiting quotient to the sheaf limit. -/
def quotientToSheafLimit :
    limitQuotient D i0 P ⟶ sheafLimit D :=
  coequalizer.desc (limitAtlasToSheafLimit D i0 P)
    (limitAtlasToSheafLimit_equalizes D i0 P)

/-- The comparison factors the quotient map through the atlas map. -/
theorem quotientToSheafLimit_spec :
    limitQuotientMap D i0 P ≫ quotientToSheafLimit D i0 P =
      limitAtlasToSheafLimit D i0 P :=
  coequalizer.π_desc _ _

/-- The comparison has the expected projection at every stage. -/
theorem quotientToSheafLimit_π (i : OrderDual I) :
    limitQuotientMap D i0 P ≫ quotientToSheafLimit D i0 P ≫ sheafLimit_π D i =
      coneFromLimitAtlas_π D i0 P i := by
  rw [← Category.assoc, quotientToSheafLimit_spec]
  exact limit.lift_π (coneFromLimitAtlas D i0 P) i

/-- The comparison from the quotient of the limiting atlas to the sheaf limit is an isomorphism. -/
theorem quotientToSheafLimit_isIso
    [h_affine : ∀ {i i' : I} (h : i ≤ i'), AlgebraicSpace.Affine (D.map (homOfLE h))] :
    IsIso (quotientToSheafLimit D i0 P) := by
  letI := limitAtlasToSheafLimit_epi D i0 P
  exact (IsColimit.nonempty_isColimit_iff_isIso_desc
    (colimit.isColimit (parallelPair (limitRelationFst D i0 P)
      (limitRelationSnd D i0 P)))).mp
    ⟨(limitRelation_isKernelPair D i0 P).toCoequalizer
      (regularEpiOfEpi (limitAtlasToSheafLimit D i0 P))⟩

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
