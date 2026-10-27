/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open Opposite

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme
namespace ExtensionByZeroComparison

variable {U X : Scheme.{u}}
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

/-- The pullback of the composite of an étale object over `U` with `j` back to `U`. -/
noncomputable abbrev diagonalPullback (V : U.Etale) : U.Etale :=
  (smallEtalePullback j).obj ((etaleRestriction j).obj V)

/-- The two legs defining the diagonal section satisfy the pullback relation. -/
theorem diagonalSection_condition (V : U.Etale) :
    𝟙 V.left ≫ ((etaleRestriction j).obj V).hom = V.hom ≫ j := by
  exact Category.id_comp _

/-- The scheme map underlying the diagonal section into `V ×_X U`. -/
noncomputable def diagonalSectionHom (V : U.Etale) :
    V.left ⟶ (diagonalPullback j V).left :=
  pullback.lift (𝟙 V.left) V.hom (diagonalSection_condition j V)

/-- The diagonal section is a morphism over `U`. -/
theorem diagonalSectionHom_over (V : U.Etale) :
    diagonalSectionHom j V ≫ (diagonalPullback j V).hom = V.hom := by
  exact pullback.lift_snd _ _ _

/-- The diagonal section, bundled in the small étale site of `U`. -/
noncomputable def diagonalSection (V : U.Etale) :
    V ⟶ diagonalPullback j V :=
  MorphismProperty.Over.homMk (diagonalSectionHom j V)
    (diagonalSectionHom_over j V)

/-- The diagonal section is an open immersion because the pullback projection is étale. -/
instance diagonalSectionHom_isOpenImmersion (V : U.Etale) :
    IsOpenImmersion (diagonalSectionHom j V) := by
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (pullback_lift_diagonal_isPullback V.hom j)
    (FormallyUnramified.isOpenImmersion_diagonal j)

/-- The diagonal section is a closed immersion because `j` is separated. -/
instance diagonalSectionHom_isClosedImmersion (V : U.Etale) :
    IsClosedImmersion (diagonalSectionHom j V) := by
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (pullback_lift_diagonal_isPullback V.hom j)
    (IsSeparated.isClosedImmersion_diagonal (f := j))

/-- The open range of the diagonal section is also closed. -/
theorem diagonalRange_isClosed (V : U.Etale) :
    IsClosed ((diagonalSectionHom j V).opensRange : Set (diagonalPullback j V).left) := by
  exact (diagonalSectionHom j V).isClosedEmbedding.isClosed_range

/-- The open complement of the clopen diagonal section. -/
noncomputable def diagonalComplement (V : U.Etale) :
    (diagonalPullback j V).left.Opens :=
  ⟨((diagonalSectionHom j V).opensRange : Set (diagonalPullback j V).left)ᶜ,
    (diagonalRange_isClosed j V).isOpen_compl⟩

/-- The diagonal-range inclusion followed by the pullback structure map is étale. -/
instance diagonalRange_hom_etale (V : U.Etale) :
    Etale ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom) := by
  infer_instance

/-- The complementary-open inclusion followed by the pullback structure map is étale. -/
instance diagonalComplement_hom_etale (V : U.Etale) :
    Etale ((diagonalComplement j V).ι ≫ (diagonalPullback j V).hom) := by
  infer_instance

/-- The diagonal range as an object of the small étale site of `U`. -/
noncomputable def diagonalRangeObject (V : U.Etale) : U.Etale :=
  MorphismProperty.Over.mk ⊤
    ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom)
    (inferInstance : Etale
      ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom))

/-- The complement of the diagonal range as an object of the small étale site of `U`. -/
noncomputable def diagonalComplementObject (V : U.Etale) : U.Etale :=
  MorphismProperty.Over.mk ⊤
    ((diagonalComplement j V).ι ≫ (diagonalPullback j V).hom)
    (inferInstance : Etale
      ((diagonalComplement j V).ι ≫ (diagonalPullback j V).hom))

/-- The diagonal-range inclusion respects the structure maps to `U`. -/
theorem diagonalRangeInclusion_over (V : U.Etale) :
    (diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom =
      (diagonalRangeObject j V).hom := by
  rfl

/-- The complementary-open inclusion respects the structure maps to `U`. -/
theorem diagonalComplementInclusion_over (V : U.Etale) :
    (diagonalComplement j V).ι ≫ (diagonalPullback j V).hom =
      (diagonalComplementObject j V).hom := by
  rfl

/-- The inclusion of the diagonal range in the pullback object. -/
noncomputable def diagonalRangeInclusion (V : U.Etale) :
    diagonalRangeObject j V ⟶ diagonalPullback j V :=
  MorphismProperty.Over.homMk (diagonalSectionHom j V).opensRange.ι
    (diagonalRangeInclusion_over j V)

/-- The inclusion of the complementary open in the pullback object. -/
noncomputable def diagonalComplementInclusion (V : U.Etale) :
    diagonalComplementObject j V ⟶ diagonalPullback j V :=
  MorphismProperty.Over.homMk (diagonalComplement j V).ι
    (diagonalComplementInclusion_over j V)

/-- The canonical range isomorphism respects the structure maps to `U`. -/
theorem diagonalRangeIso_over (V : U.Etale) :
    (diagonalSectionHom j V).isoOpensRange.hom ≫ (diagonalRangeObject j V).hom =
      V.hom := by
  change (diagonalSectionHom j V).isoOpensRange.hom ≫
    ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom) = V.hom
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, diagonalSectionHom_over]

/-- The source of the diagonal section is canonically its open range, over `U`. -/
noncomputable def diagonalRangeIso (V : U.Etale) :
    V ≅ diagonalRangeObject j V :=
  MorphismProperty.Over.isoMk (diagonalSectionHom j V).isoOpensRange
    (diagonalRangeIso_over j V)

variable (A : Type (w + 1)) [Category.{w} A] [HasZeroMorphisms A]

/-- The two members of the clopen cover by the diagonal range and its complement. -/
noncomputable def diagonalCoverObject (V : U.Etale) : Bool → U.Etale
  | false => diagonalRangeObject j V
  | true => diagonalComplementObject j V

/-- The two inclusions in the clopen cover by the diagonal range and its complement. -/
noncomputable def diagonalCoverMap (V : U.Etale) :
    ∀ i : Bool, diagonalCoverObject j V i ⟶ diagonalPullback j V
  | false => diagonalRangeInclusion j V
  | true => diagonalComplementInclusion j V

/-- The diagonal range and its complement cover the pullback object in the small étale
topology. -/
theorem diagonalCover_mem (V : U.Etale) :
    Sieve.ofArrows (diagonalCoverObject j V) (diagonalCoverMap j V) ∈
      U.smallEtaleTopology (diagonalPullback j V) := by
  rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
  intro point
  by_cases membership : point ∈ (diagonalSectionHom j V).opensRange
  · exact Set.mem_iUnion.mpr ⟨false, ⟨⟨point, membership⟩, rfl⟩⟩
  · exact Set.mem_iUnion.mpr ⟨true, ⟨⟨point, membership⟩, rfl⟩⟩

/-- On the diagonal member use the original section; on the complement use zero. -/
noncomputable def diagonalExtensionLocalMap
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    ∀ i : Bool, F.obj.obj (op V) ⟶ F.obj.obj (op (diagonalCoverObject j V i))
  | false => F.obj.map (diagonalRangeIso j V).inv.op
  | true => 0

/-- The original section on the diagonal and zero on the complement agree on every overlap. -/
theorem diagonalExtensionLocalMap_compatible
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    ∀ (W : U.Etale) (i k : Bool)
      (a : W ⟶ diagonalCoverObject j V i)
      (b : W ⟶ diagonalCoverObject j V k),
      a ≫ diagonalCoverMap j V i = b ≫ diagonalCoverMap j V k →
        diagonalExtensionLocalMap j A F V i ≫ F.obj.map a.op =
          diagonalExtensionLocalMap j A F V k ≫ F.obj.map b.op := by
  intro W
  have emptyOverlap (rangeMap : W ⟶ diagonalRangeObject j V)
      (complementMap : W ⟶ diagonalComplementObject j V)
      (agreement : rangeMap ≫ diagonalRangeInclusion j V =
        complementMap ≫ diagonalComplementInclusion j V) :
      ⊥ ∈ U.smallEtaleTopology W := by
    have underlying : rangeMap.left ≫ (diagonalSectionHom j V).opensRange.ι =
        complementMap.left ≫ (diagonalComplement j V).ι :=
      congrArg (fun arrow => arrow.left) agreement
    have noPoint (point : W.left) : False := by
      have pointEquality : (rangeMap.left point).val = (complementMap.left point).val :=
        congrArg (fun arrow => arrow point) underlying
      exact (complementMap.left point).property
        (pointEquality ▸ (rangeMap.left point).property)
    have emptyCover : Sieve.ofArrows (fun index : Empty => nomatch index)
        (fun index : Empty => nomatch index) ∈ U.smallEtaleTopology W := by
      rw [ofArrows_mem_smallEtaleTopology_iff, Set.eq_univ_iff_forall]
      intro point
      exact (noPoint point).elim
    simpa [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty] using emptyCover
  intro first second rangeMap complementMap agreement
  cases first <;> cases second
  · have mapsEqual : rangeMap = complementMap := by
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono (diagonalSectionHom j V).opensRange.ι).mp
      exact congrArg (fun arrow => arrow.left) agreement
    rw [mapsEqual]
  · exact (F.isTerminalOfBotCover W (emptyOverlap rangeMap complementMap agreement)).hom_ext _ _
  · exact (F.isTerminalOfBotCover W
      (emptyOverlap complementMap rangeMap agreement.symm)).hom_ext _ _
  · simp [diagonalExtensionLocalMap]

/-- Extend a section on the diagonal range by zero on its open complement, using the
canonical amalgamation supplied by the sheaf condition. -/
noncomputable def diagonalExtensionMap
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    F.obj.obj (op V) ⟶ F.obj.obj (op (diagonalPullback j V)) :=
  F.property.amalgamateOfArrows (diagonalCoverMap j V) (diagonalCover_mem j V)
    (diagonalExtensionLocalMap j A F V)
    (fun {W i k} a b h ↦
      diagonalExtensionLocalMap_compatible j A F V W i k a b h)

/-- Restricting the diagonal extension back to the diagonal range recovers the original
section through the canonical range isomorphism. -/
theorem diagonalExtensionMap_range
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    diagonalExtensionMap j A F V ≫ F.obj.map (diagonalRangeInclusion j V).op =
      F.obj.map (diagonalRangeIso j V).inv.op := by
  exact F.property.amalgamateOfArrows_map _ _ _ _ false

/-- Restricting the diagonal extension to the complementary open is zero. -/
theorem diagonalExtensionMap_complement
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    diagonalExtensionMap j A F V ≫ F.obj.map (diagonalComplementInclusion j V).op = 0 := by
  exact F.property.amalgamateOfArrows_map _ _ _ _ true

/-- Extending by zero along the diagonal commutes with morphisms of sheaves. -/
theorem diagonalExtensionMap_naturality
    {F G : Sheaf U.smallEtaleTopology A} (α : F ⟶ G) (V : U.Etale) :
    α.hom.app (op V) ≫ diagonalExtensionMap j A G V =
      diagonalExtensionMap j A F V ≫ α.hom.app (op (diagonalPullback j V)) := by
  apply G.property.hom_ext_ofArrows _ (diagonalCover_mem j V)
  intro i
  cases i
  · change (α.hom.app (op V) ≫ diagonalExtensionMap j A G V) ≫
      G.obj.map (diagonalRangeInclusion j V).op =
        (diagonalExtensionMap j A F V ≫ α.hom.app (op (diagonalPullback j V))) ≫
          G.obj.map (diagonalRangeInclusion j V).op
    rw [Category.assoc, diagonalExtensionMap_range]
    rw [Category.assoc, ← α.hom.naturality (diagonalRangeInclusion j V).op,
      ← Category.assoc, diagonalExtensionMap_range]
    exact (α.hom.naturality _).symm
  · change (α.hom.app (op V) ≫ diagonalExtensionMap j A G V) ≫
      G.obj.map (diagonalComplementInclusion j V).op =
        (diagonalExtensionMap j A F V ≫ α.hom.app (op (diagonalPullback j V))) ≫
          G.obj.map (diagonalComplementInclusion j V).op
    rw [Category.assoc, diagonalExtensionMap_complement]
    rw [Category.assoc, ← α.hom.naturality (diagonalComplementInclusion j V).op,
      ← Category.assoc, diagonalExtensionMap_complement]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal section commutes with morphisms of étale objects over `U`. -/
theorem diagonalSection_naturality {V W : U.Etale} (f : V ⟶ W) :
    diagonalSection j V ≫ (smallEtalePullback j).map ((etaleRestriction j).map f) =
      f ≫ diagonalSection j W := by
  apply MorphismProperty.Over.Hom.ext
  change diagonalSectionHom j V ≫
      ((smallEtalePullback j).map ((etaleRestriction j).map f)).left =
    f.left ≫ diagonalSectionHom j W
  apply pullback.hom_ext
  · simp only [diagonalSectionHom, MorphismProperty.Over.pullback_map_left,
      Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
    change 𝟙 V.left ≫ f.left = f.left ≫ 𝟙 W.left
    simp
  · simpa [diagonalSectionHom, MorphismProperty.Over.pullback_map_left] using
      (MorphismProperty.Over.w f).symm

set_option backward.isDefEq.respectTransparency false in
/-- The naturality square of the diagonal sections is cartesian. -/
theorem diagonalSection_isPullback {V W : U.Etale} (f : V ⟶ W) :
    IsPullback (diagonalSectionHom j V) f.left
      ((smallEtalePullback j).map ((etaleRestriction j).map f)).left
      (diagonalSectionHom j W) := by
  let g := (smallEtalePullback j).map ((etaleRestriction j).map f)
  have hfst : g.left ≫ pullback.fst ((etaleRestriction j).obj W).hom j =
      pullback.fst ((etaleRestriction j).obj V).hom j ≫ f.left :=
    pullback.lift_fst _ _ _
  have hsnd : g.left ≫ pullback.snd ((etaleRestriction j).obj W).hom j =
      pullback.snd ((etaleRestriction j).obj V).hom j :=
    pullback.lift_snd _ _ _
  have hbase : f.left ≫ ((etaleRestriction j).obj W).hom =
      ((etaleRestriction j).obj V).hom :=
    MorphismProperty.Over.w ((etaleRestriction j).map f)
  have hp : IsPullback (pullback.fst ((etaleRestriction j).obj V).hom j) g.left
      f.left (pullback.fst ((etaleRestriction j).obj W).hom j) := by
    apply IsPullback.of_bot _ hfst.symm
      (IsPullback.of_hasPullback ((etaleRestriction j).obj W).hom j)
    rw [hsnd, hbase]
    exact IsPullback.of_hasPullback ((etaleRestriction j).obj V).hom j
  apply IsPullback.of_right _ _ hp
  · simpa [diagonalSectionHom] using (IsPullback.of_id_fst (f := f.left))
  · exact congrArg (fun k => k.left) (diagonalSection_naturality j f)

/-- The inverse image of a diagonal range is the diagonal range of the source. -/
theorem diagonalRange_preimage {V W : U.Etale} (f : V ⟶ W) :
    Set.range (diagonalSectionHom j V) =
      ((smallEtalePullback j).map ((etaleRestriction j).map f)).left ⁻¹'
        Set.range (diagonalSectionHom j W) := by
  simpa using image_preimage_eq_of_isPullback (diagonalSection_isPullback j f).flip Set.univ

set_option backward.isDefEq.respectTransparency false in
/-- Extending by zero along the diagonal commutes with restriction on the small étale site. -/
theorem diagonalExtensionMap_restriction
    (F : Sheaf U.smallEtaleTopology A) {V W : U.Etale} (f : V ⟶ W) :
    F.obj.map f.op ≫ diagonalExtensionMap j A F V =
      diagonalExtensionMap j A F W ≫
        F.obj.map ((smallEtalePullback j).map ((etaleRestriction j).map f)).op := by
  let g := (smallEtalePullback j).map ((etaleRestriction j).map f)
  have iso_fac (Z : U.Etale) :
      (diagonalRangeIso j Z).hom ≫ diagonalRangeInclusion j Z = diagonalSection j Z := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.Hom.isoOpensRange_hom_ι (diagonalSectionHom j Z)
  let r : diagonalRangeObject j V ⟶ diagonalRangeObject j W :=
    (diagonalRangeIso j V).inv ≫ f ≫ (diagonalRangeIso j W).hom
  have rfac : r ≫ diagonalRangeInclusion j W = diagonalRangeInclusion j V ≫ g := by
    calc
      r ≫ diagonalRangeInclusion j W =
          (diagonalRangeIso j V).inv ≫ f ≫ diagonalSection j W := by
        simp only [r, Category.assoc, iso_fac]
      _ = (diagonalRangeIso j V).inv ≫ diagonalSection j V ≫ g := by
        rw [diagonalSection_naturality j f]
      _ = diagonalRangeInclusion j V ≫ g := by
        rw [← iso_fac V]
        simp
  have hc : diagonalComplement j V ≤ g.left ⁻¹ᵁ diagonalComplement j W := by
    intro p hp
    change p ∉ Set.range (diagonalSectionHom j V) at hp
    change g.left p ∉ Set.range (diagonalSectionHom j W)
    rwa [diagonalRange_preimage j f] at hp
  let cHom := g.left.resLE (diagonalComplement j W) (diagonalComplement j V) hc
  have c_over : cHom ≫ (diagonalComplementObject j W).hom =
      (diagonalComplementObject j V).hom := by
    change cHom ≫ ((diagonalComplement j W).ι ≫ (diagonalPullback j W).hom) =
      (diagonalComplement j V).ι ≫ (diagonalPullback j V).hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      MorphismProperty.Over.w g]
  let c : diagonalComplementObject j V ⟶ diagonalComplementObject j W :=
    MorphismProperty.Over.homMk cHom c_over
  have cfac : c ≫ diagonalComplementInclusion j W =
      diagonalComplementInclusion j V ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.Hom.resLE_comp_ι g.left hc
  apply F.property.hom_ext_ofArrows _ (diagonalCover_mem j V)
  intro i
  cases i
  · change (F.obj.map f.op ≫ diagonalExtensionMap j A F V) ≫
        F.obj.map (diagonalRangeInclusion j V).op =
      (diagonalExtensionMap j A F W ≫ F.obj.map g.op) ≫
        F.obj.map (diagonalRangeInclusion j V).op
    calc
      (F.obj.map f.op ≫ diagonalExtensionMap j A F V) ≫
          F.obj.map (diagonalRangeInclusion j V).op =
        F.obj.map f.op ≫ F.obj.map (diagonalRangeIso j V).inv.op := by
          rw [Category.assoc, diagonalExtensionMap_range]
      _ = F.obj.map ((diagonalRangeIso j V).inv ≫ f).op := by
        rw [op_comp, F.obj.map_comp]
      _ = F.obj.map (diagonalRangeIso j W).inv.op ≫ F.obj.map r.op := by
        simp [r, ← F.obj.map_comp, ← op_comp]
      _ = (diagonalExtensionMap j A F W ≫
          F.obj.map (diagonalRangeInclusion j W).op) ≫ F.obj.map r.op := by
        rw [diagonalExtensionMap_range]
      _ = (diagonalExtensionMap j A F W ≫ F.obj.map g.op) ≫
          F.obj.map (diagonalRangeInclusion j V).op := by
        simp only [Category.assoc, ← F.obj.map_comp, ← op_comp, rfac]
  · change (F.obj.map f.op ≫ diagonalExtensionMap j A F V) ≫
        F.obj.map (diagonalComplementInclusion j V).op =
      (diagonalExtensionMap j A F W ≫ F.obj.map g.op) ≫
        F.obj.map (diagonalComplementInclusion j V).op
    rw [Category.assoc, diagonalExtensionMap_complement, comp_zero]
    rw [Category.assoc, ← F.obj.map_comp, ← op_comp, ← cfac,
      op_comp, F.obj.map_comp, ← Category.assoc, diagonalExtensionMap_complement,
      zero_comp]

end ExtensionByZeroComparison

open ExtensionByZeroComparison

variable {U X : Scheme.{u}}
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/-- The presheaf unit that extends a section by zero along the clopen diagonal. -/
noncomputable def abelianExtensionByZeroPresheafUnit
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    F.obj ⟶ (etaleRestriction j).op ⋙ (smallEtalePullback j).op ⋙ F.obj where
  app V := diagonalExtensionMap j AddCommGrpCat.{w} F V.unop
  naturality := by
    intro V W f
    exact diagonalExtensionMap_restriction j AddCommGrpCat.{w} F f.unop

/-- The presheaf comparison induced by the clopen-diagonal extension maps. -/
noncomputable def abelianExtensionByZeroPresheafMap
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    (etaleRestriction j).op.leftKanExtension F.obj ⟶
      (smallEtalePullback j).op ⋙ F.obj :=
  (((etaleRestriction j).op.lanAdjunction AddCommGrpCat.{w}).homEquiv
    F.obj ((smallEtalePullback j).op ⋙ F.obj)).symm
      (abelianExtensionByZeroPresheafUnit j F)

/-- The sheaf-level component of the separated-étale comparison. -/
noncomputable def abelianExtensionByZeroToDirectImageApp
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    (abelianExtensionByZero j).obj F ⟶
      ((smallEtalePullback j).sheafPushforwardContinuous
        AddCommGrpCat.{w} X.smallEtaleTopology U.smallEtaleTopology).obj F :=
  (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
      AddCommGrpCat.{w} U.smallEtaleTopology X.smallEtaleTopology).hom.app F ≫
    Sheaf.homEquiv.symm
      (sheafifyLift X.smallEtaleTopology
        (abelianExtensionByZeroPresheafMap j F)
        (((smallEtalePullback j).sheafPushforwardContinuous
          AddCommGrpCat.{w} X.smallEtaleTopology U.smallEtaleTopology).obj F).property)

/-- The concrete natural transformation comparing abelian extension by zero with
small étale direct image for a separated étale morphism. -/
noncomputable def abelianExtensionByZeroToDirectImage :
    abelianExtensionByZero j ⟶
      (smallEtalePullback j).sheafPushforwardContinuous
        AddCommGrpCat.{w} X.smallEtaleTopology U.smallEtaleTopology where
  app := abelianExtensionByZeroToDirectImageApp j
  naturality := by
    intro F G α
    have presheaf_naturality :
        (etaleRestriction j).op.lan.map α.hom ≫
            abelianExtensionByZeroPresheafMap j G =
          abelianExtensionByZeroPresheafMap j F ≫
            whiskerLeft (smallEtalePullback j).op α.hom := by
      unfold abelianExtensionByZeroPresheafMap
      rw [← Adjunction.homEquiv_naturality_left_symm]
      erw [← ((etaleRestriction j).op.lanAdjunction AddCommGrpCat.{w}).homEquiv_naturality_right_symm
          (abelianExtensionByZeroPresheafUnit j F)
          (whiskerLeft (smallEtalePullback j).op α.hom)]
      congr 1
      apply NatTrans.ext
      funext V
      exact diagonalExtensionMap_naturality j AddCommGrpCat.{w} α V.unop
    dsimp only [abelianExtensionByZeroToDirectImageApp]
    rw [← Category.assoc,
      (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
        AddCommGrpCat.{w} U.smallEtaleTopology X.smallEtaleTopology).hom.naturality α]
    simp only [Category.assoc]
    congr 1
    apply Sheaf.hom_ext
    change sheafifyMap X.smallEtaleTopology ((etaleRestriction j).op.lan.map α.hom) ≫
        sheafifyLift X.smallEtaleTopology (abelianExtensionByZeroPresheafMap j G) _ =
      sheafifyLift X.smallEtaleTopology (abelianExtensionByZeroPresheafMap j F) _ ≫
        whiskerLeft (smallEtalePullback j).op α.hom
    rw [sheafifyMap_sheafifyLift, presheaf_naturality]
    exact sheafifyLift_comp _ _ _ _ _

variable {Λ : Type w} [Ring Λ]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/-- The module-presheaf unit that extends a section by zero along the clopen diagonal. -/
noncomputable def moduleExtensionByZeroPresheafUnit
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    F.obj ⟶ (etaleRestriction j).op ⋙ (smallEtalePullback j).op ⋙ F.obj where
  app V := diagonalExtensionMap j (ModuleCat.{w} Λ) F V.unop
  naturality := by
    intro V W f
    exact diagonalExtensionMap_restriction j (ModuleCat.{w} Λ) F f.unop

/-- The module-presheaf comparison induced by the clopen-diagonal extension maps. -/
noncomputable def moduleExtensionByZeroPresheafMap
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    (etaleRestriction j).op.leftKanExtension F.obj ⟶
      (smallEtalePullback j).op ⋙ F.obj :=
  (((etaleRestriction j).op.lanAdjunction (ModuleCat.{w} Λ)).homEquiv
    F.obj ((smallEtalePullback j).op ⋙ F.obj)).symm
      (moduleExtensionByZeroPresheafUnit j F)

/-- The sheaf-level module component of the separated-étale comparison. -/
noncomputable def moduleExtensionByZeroToDirectImageApp
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    (moduleExtensionByZero j).obj F ⟶
      ((smallEtalePullback j).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) X.smallEtaleTopology U.smallEtaleTopology).obj F :=
  (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
      (ModuleCat.{w} Λ) U.smallEtaleTopology X.smallEtaleTopology).hom.app F ≫
    Sheaf.homEquiv.symm
      (sheafifyLift X.smallEtaleTopology
        (moduleExtensionByZeroPresheafMap j F)
        (((smallEtalePullback j).sheafPushforwardContinuous
          (ModuleCat.{w} Λ) X.smallEtaleTopology U.smallEtaleTopology).obj F).property)

/-- The concrete natural transformation comparing module extension by zero with
small étale direct image for a separated étale morphism. -/
noncomputable def moduleExtensionByZeroToDirectImage :
    moduleExtensionByZero j ⟶
      (smallEtalePullback j).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) X.smallEtaleTopology U.smallEtaleTopology where
  app := moduleExtensionByZeroToDirectImageApp j
  naturality := by
    intro F G α
    have presheaf_naturality :
        (etaleRestriction j).op.lan.map α.hom ≫
            moduleExtensionByZeroPresheafMap j G =
          moduleExtensionByZeroPresheafMap j F ≫
            whiskerLeft (smallEtalePullback j).op α.hom := by
      unfold moduleExtensionByZeroPresheafMap
      rw [← Adjunction.homEquiv_naturality_left_symm]
      erw [← ((etaleRestriction j).op.lanAdjunction (ModuleCat.{w} Λ)).homEquiv_naturality_right_symm
          (moduleExtensionByZeroPresheafUnit j F)
          (whiskerLeft (smallEtalePullback j).op α.hom)]
      congr 1
      apply NatTrans.ext
      funext V
      exact diagonalExtensionMap_naturality j (ModuleCat.{w} Λ) α V.unop
    dsimp only [moduleExtensionByZeroToDirectImageApp]
    rw [← Category.assoc,
      (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
        (ModuleCat.{w} Λ) U.smallEtaleTopology X.smallEtaleTopology).hom.naturality α]
    simp only [Category.assoc]
    congr 1
    apply Sheaf.hom_ext
    change sheafifyMap X.smallEtaleTopology ((etaleRestriction j).op.lan.map α.hom) ≫
        sheafifyLift X.smallEtaleTopology (moduleExtensionByZeroPresheafMap j G) _ =
      sheafifyLift X.smallEtaleTopology (moduleExtensionByZeroPresheafMap j F) _ ≫
        whiskerLeft (smallEtalePullback j).op α.hom
    rw [sheafifyMap_sheafifyLift, presheaf_naturality]
    exact sheafifyLift_comp _ _ _ _ _

section AbelianMono

variable {U X : Scheme.{u}}
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/-- Each component of the abelian extension-by-zero comparison is a monomorphism. -/
instance abelianExtensionByZeroToDirectImage_app_mono
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    Mono ((abelianExtensionByZeroToDirectImage j).app F) := sorry

end AbelianMono

section ModuleMono

variable {U X : Scheme.{u}}
variable {Λ : Type w} [Ring Λ]
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/-- Each component of the module extension-by-zero comparison is a monomorphism. -/
instance moduleExtensionByZeroToDirectImage_app_mono
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    Mono ((moduleExtensionByZeroToDirectImage j).app F) := sorry

end ModuleMono

/-- For a finite étale morphism, each component of the abelian extension-by-zero
comparison with small étale direct image is an isomorphism. -/
instance abelianExtensionByZeroToDirectImage_app_isIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsFinite j] [Etale j]
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    IsIso ((abelianExtensionByZeroToDirectImage j).app F) := sorry

/-- For a finite étale morphism, each component of the `Λ`-module extension-by-zero
comparison with small étale direct image is an isomorphism. -/
instance moduleExtensionByZeroToDirectImage_app_isIso
    {U X : Scheme.{u}} {Λ : Type w} [Ring Λ] (j : U ⟶ X) [IsFinite j] [Etale j]
    [∀ G : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    IsIso ((moduleExtensionByZeroToDirectImage j).app F) := sorry

end AlgebraicGeometry.Scheme
