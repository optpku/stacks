/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.TopologicalInvariance
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# The doubled affine line and its étale cover

This module defines the affine line with zero doubled by gluing two copies of `𝔸¹_k`
along `D(x)`, together with its two affine charts and the comparison `1 ⨿ (-1)`
toward `𝔸¹_k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine

/-- The base scheme `S = Spec k`. -/
abbrev base (k : Type u) [Field k] : Scheme.{u} := AffineLineInvolution.base k

/-- The affine line with zero doubled, as a scheme. -/
abbrev doubledScheme (k : Type u) [Field k] : Scheme.{u} :=
  doubleAlong (AffineLineInvolution.puncturedOpen k)

/-- Each canonical chart of the doubled line is compatible with the structure morphism. -/
theorem chartMap_w (k : Type u) [Field k] (i : Fin 2) :
    DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i ≫
        DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
          (AffineLineInvolution.cover k).hom =
      (AffineLineInvolution.cover k).hom := by
  have h :
      DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i ≫
          DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) = 𝟙 _ :=
    Multicoequalizer.π_desc _ _ _ _ _
  rw [← Category.assoc, h, Category.id_comp]

/-- The affine line with zero doubled, as a scheme over `Spec k`. -/
def cover (k : Type u) [Field k] : Over (base k) :=
  Over.mk (DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
    (AffineLineInvolution.cover k).hom)

/-- The underlying scheme of `cover k` is the doubled affine line. -/
theorem cover_left (k : Type u) [Field k] :
    (cover k).left = doubledScheme k := rfl

/-- The structure morphism of `cover k` is the fold followed by `𝔸¹_k ⟶ Spec k`. -/
theorem cover_hom (k : Type u) [Field k] :
    (cover k).hom =
      DoubleAlong.fold (AffineLineInvolution.puncturedOpen k) ≫
        (AffineLineInvolution.cover k).hom := rfl

/-- The open immersion of the `i`-th affine-line chart into the doubled line, over `Spec k`. -/
def chartHom (k : Type u) [Field k] (i : Fin 2) :
    AffineLineInvolution.cover k ⟶ cover k :=
  Over.homMk (DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i)
    (chartMap_w k i)

/-- The underlying scheme map of `chartHom k i` is the canonical doubled-scheme chart map. -/
theorem chartHom_left (k : Type u) [Field k] (i : Fin 2) :
    (chartHom k i).left =
      DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) i := rfl

/-- The coproduct of the two affine-line charts, as a scheme over `Spec k`. -/
def chartCoproduct (k : Type u) [Field k] : Over (base k) :=
  AffineLineInvolution.cover k ⨿ AffineLineInvolution.cover k

/-- The two chart immersions, as a morphism from the coproduct of charts to `Y`. -/
def atlasCoproduct (k : Type u) [Field k] : chartCoproduct k ⟶ cover k :=
  coprod.desc (chartHom k 0) (chartHom k 1)

/-- The map `1 ⨿ (-1)` from the coproduct of charts to `𝔸¹_k`. -/
def toAffineCoproduct (k : Type u) [Field k] :
    chartCoproduct k ⟶ AffineLineInvolution.cover k :=
  coprod.desc (𝟙 _) (AffineLineInvolution.involution k)


end AlgebraicGeometry.AlgebraicSpace.DoubledAffineLine

namespace AlgebraicGeometry.AlgebraicSpace

/-- The universal homeomorphism from the affine-line involution space to the affine line
is not relatively representable. -/
theorem AffineLineInvolution.not_relativelyRepresentable_toAffineLine
    (k : Type u) [Field k] [NeZero (2 : k)] :
    ¬ uliftYoneda.{u + 1}.relativelyRepresentable
        (AffineLineInvolution.toAffineLine k).hom := by
  intro h
  let F : Over (AffineLineInvolution.base k) ⥤
      (Over (AffineLineInvolution.base k))ᵒᵖ ⥤ Type (u + 1) := uliftYoneda.{u + 1}
  let P : MorphismProperty (Over (AffineLineInvolution.base k)) :=
    MorphismProperty.over (@IsImmersion)
  let R := P.relative F
  haveI : P.IsStableUnderBaseChange := {
    of_isPullback sq hg :=
      MorphismProperty.of_isPullback (P := @IsImmersion)
        (sq.map (Over.forget (AffineLineInvolution.base k))) hg }
  -- A representable morphism to a represented target has represented source.
  let a := h.pullback (𝟙 _)
  haveI : IsIso (h.fst (𝟙 _)) :=
    (h.isPullback (𝟙 _)).isIso_fst_of_isIso (by
      change IsIso (𝟙 (F.obj (AffineLineInvolution.cover k)))
      infer_instance)
  let e : F.obj a ≅ (AffineLineInvolution.sheafOfPoints k).obj := asIso (h.fst (𝟙 _))
  -- The diagonal of a scheme over the base is an immersion.
  have hd : P (diag a) := by
    change IsImmersion (diag a).left
    let c := Over.prodLeftIsoPullback a a
    have hc : (diag a).left ≫ c.hom = pullback.diagonal a.hom := by
      apply pullback.hom_ext
      · simpa [c, diag, ← Over.comp_left] using
          congrArg (fun f : a ⟶ a ↦ f.left) (prod.lift_fst (𝟙 a) (𝟙 a))
      · simpa [c, diag, ← Over.comp_left] using
          congrArg (fun f : a ⟶ a ↦ f.left) (prod.lift_snd (𝟙 a) (𝟙 a))
    have hd' : IsImmersion ((diag a).left ≫ c.hom) := by
      rw [hc]
      infer_instance
    exact (MorphismProperty.cancel_right_of_respectsIso @IsImmersion _ c.hom).mp hd'
  have hd' : R (F.map (diag a) ≫ prodComparison F a a) :=
    MorphismProperty.RespectsIso.postcomp R _ _ (MorphismProperty.relative_map hd)
  have hc : F.map (diag a) ≫ prodComparison F a a = diag (F.obj a) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst, ← F.map_comp,
        diag, prod.lift_fst, F.map_id]
    · simp only [Category.assoc, prodComparison_snd, ← F.map_comp,
        diag, prod.lift_snd, F.map_id]
  have hd'' : R (diag (F.obj a)) := hc ▸ hd'
  have hx : R (e.hom ≫ diag (AffineLineInvolution.sheafOfPoints k).obj) :=
    prod.diag_map e.hom ▸
      MorphismProperty.RespectsIso.postcomp R _ _ hd''
  exact AffineLineInvolution.not_isImmersion_diag_sheafOfPoints k
    ((R.cancel_left_of_respectsIso e.hom _).mp hx)

/-- Pullback along a universal homeomorphism of algebraic spaces need not induce an
equivalence of spaces-étale sites. -/
theorem not_spacesEtalePullback_isEquivalence_of_universalHomeomorphism :
    ¬ ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
        [UniversalHomeomorphism f], (spacesEtalePullback f).IsEquivalence :=
  sorry

namespace DoubledAffineLine


/-- The type of morphisms of fppf sheaves from the doubled affine line `Y` to the
involution space `X`. -/
abbrev atlasHom (k : Type u) [Field k] :=
  (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶
    AffineLineInvolution.sheafOfPoints k

/-- The chart restrictions used to glue a morphism from the doubled affine line to the
involution space: the identity on the first
affine chart and `x ↦ -x` on the second. -/
structure ChartRestrictions {k : Type u} [Field k] (f : atlasHom k) : Prop where
  /-- The first chart restricts to the atlas `𝔸¹_k ⟶ X`. -/
  chart0 :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
      AffineLineInvolution.atlas k
  /-- The second chart restricts to negation followed by the atlas `𝔸¹_k ⟶ X`. -/
  chart1 :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
          (AffineLineInvolution.involution k) ≫
        AffineLineInvolution.atlas k

/-- Package the two chart restrictions of a morphism `Y ⟶ X`. -/
def ChartRestrictions.of {k : Type u} [Field k] (f : atlasHom k)
    (chart0 :
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
        AffineLineInvolution.atlas k)
    (chart1 :
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
            (AffineLineInvolution.involution k) ≫
          AffineLineInvolution.atlas k) :
    ChartRestrictions f :=
  ⟨chart0, chart1⟩

/-- `ChartRestrictions f` is equivalent to its two chart identities. -/
theorem ChartRestrictions.iff {k : Type u} [Field k] (f : atlasHom k) :
    ChartRestrictions f ↔
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 0) ≫ f =
          AffineLineInvolution.atlas k ∧
        (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (chartHom k 1) ≫ f =
          (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
              (AffineLineInvolution.involution k) ≫
            AffineLineInvolution.atlas k :=
  ⟨fun h ↦ ⟨h.chart0, h.chart1⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- If `k` is algebraically closed of characteristic zero, then `𝔸¹_k`
has no nontrivial connected finite étale covering. -/
@[stacks 05ZI]
theorem isIso_of_connected_finiteEtale
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    {U : Over (base k)} (f : U ⟶ AffineLineInvolution.cover k)
    [AlgebraicGeometry.IsFinite f.left] [AlgebraicGeometry.Etale f.left]
    [AlgebraicGeometry.Surjective f.left] [ConnectedSpace U.left] :
    IsIso f :=
  sorry

/-- The two chart restrictions glue uniquely to a morphism from the doubled affine line to the involution space. -/
@[stacks 05ZI]
theorem existsUnique_atlasHom (k : Type u) [Field k] [NeZero (2 : k)] :
    ∃! f : atlasHom k, ChartRestrictions f :=
  sorry

/-- For a morphism glued from the two charts, the square with vertices `Y`,
`Y₁ ⨿ Y₂`, `X`, and `𝔸¹_k` is cartesian. -/
@[stacks 05ZI]
theorem atlasSquare_isPullback (k : Type u) [Field k] [NeZero (2 : k)]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    IsPullback
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (atlasCoproduct k))
      ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (toAffineCoproduct k))
      f (AffineLineInvolution.atlas k) :=
  sorry

/-- A morphism glued from the two charts is finite étale. -/
@[stacks 05ZI]
theorem finiteEtale_atlasHom (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    (MorphismProperty.over
        (@AlgebraicGeometry.IsFinite ⊓ @AlgebraicGeometry.Etale)).relative
      uliftYoneda.{u + 1} f.hom :=
  sorry

/-- A morphism glued from the two charts is finite locally free of rank `2`
relative to `uliftYoneda`. -/
@[stacks 05ZI]
theorem finiteLocallyFreeOfRank_atlasHom
    (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    (MorphismProperty.over
        ((fun _ _ g ↦ IsFiniteLocallyFreeOfRank g 2) :
          MorphismProperty Scheme.{u})).relative
      uliftYoneda.{u + 1} f.hom :=
  sorry

/-- The comparison `1 ⨿ (-1) : 𝔸¹_k ⨿ 𝔸¹_k ⟶ 𝔸¹_k` is finite locally free of rank `2`. -/
theorem finiteLocallyFreeOfRank_toAffineCoproduct
    (k : Type u) [Field k] [CharZero k] :
    IsFiniteLocallyFreeOfRank (toAffineCoproduct k).left 2 :=
  sorry

/-- The doubled affine line is connected. -/
@[stacks 05ZI]
theorem connected_cover (k : Type u) [Field k] :
    ConnectedSpace (cover k).left := by
  haveI : ConnectedSpace (AffineLineInvolution.cover k).left := by
    change ConnectedSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of k)))
    infer_instance
  let s : base k ⟶ (AffineLineInvolution.cover k).left :=
    AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 1)
  have hs : s ⁻¹ᵁ AffineLineInvolution.puncturedOpen k = ⊤ := by
    change s ⁻¹ᵁ (AffineLineInvolution.cover k).left.basicOpen
      (AffineLineInvolution.coord k) = ⊤
    rw [Scheme.preimage_basicOpen_top]
    change (base k).basicOpen
      ((AffineSpace.homOfVector (𝟙 (base k)) (fun _ : ULift.{u} (Fin 1) ↦ 1)).appTop
        (AffineSpace.coord (base k) (ULift.up (0 : Fin 1)))) = ⊤
    rw [AffineSpace.homOfVector_appTop_coord, Scheme.basicOpen_one]
  let x := s (default : base k)
  have hx : x ∈ AffineLineInvolution.puncturedOpen k := by
    change (default : base k) ∈ s ⁻¹ᵁ AffineLineInvolution.puncturedOpen k
    rw [hs]
    trivial
  have hglue :
      DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 0 x =
        DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 1 x := by
    have h := (DoubleAlong.glueData (AffineLineInvolution.puncturedOpen k)).glue_condition
      (ULift.up (0 : Fin 2)) (ULift.up (1 : Fin 2))
    have h' :
        (AffineLineInvolution.puncturedOpen k).ι ≫
            DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 0 =
          (AffineLineInvolution.puncturedOpen k).ι ≫
            DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 1 := by
      simp [DoubleAlong.glueData, DoubleAlong.Impl.glueData,
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
        DoubleAlong.Impl.glueData', DoubleAlong.Impl.glueT, DoubleAlong.Impl.glueF] at h
      exact (cancel_epi _).mp h.symm
    simpa using congrArg
      (fun f : (AffineLineInvolution.puncturedOpen k).toScheme ⟶ doubledScheme k ↦
        f ⟨x, hx⟩) h'
  have hcover :
      Set.range (DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 0) ∪
          Set.range (DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 1) =
        Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨⟨i⟩, z, hz⟩ :=
      (DoubleAlong.glueData (AffineLineInvolution.puncturedOpen k)).ι_jointly_surjective y
    fin_cases i
    · exact Or.inl ⟨z, hz⟩
    · exact Or.inr ⟨z, hz⟩
  apply connectedSpace_iff_univ.mpr
  change _root_.IsConnected (Set.univ : Set (doubledScheme k))
  rw [← hcover]
  exact IsConnected.union ⟨_, ⟨x, rfl⟩, ⟨x, hglue.symm⟩⟩
    (isConnected_range
      (DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 0).continuous)
    (isConnected_range
      (DoubleAlong.chartMap (AffineLineInvolution.puncturedOpen k) 1).continuous)

/-- A morphism glued from the two charts is nontrivial. -/
@[stacks 05ZI]
theorem not_isIso_atlasHom (k : Type u) [Field k] [CharZero k]
    (f : atlasHom k) (hf : ChartRestrictions f) :
    ¬ IsIso f := by
  intro h
  letI := h
  haveI : IsIso f.hom := inferInstance
  obtain ⟨g, hg⟩ := uliftYoneda.{u + 1}.map_surjective
    (f.hom ≫ (AffineLineInvolution.toAffineLine k).hom)
  have hrep : uliftYoneda.{u + 1}.relativelyRepresentable
      (f.hom ≫ (AffineLineInvolution.toAffineLine k).hom) :=
    hg ▸ Functor.relativelyRepresentable.map _ g
  exact AffineLineInvolution.not_relativelyRepresentable_toAffineLine k
    ((uliftYoneda.{u + 1}.relativelyRepresentable.cancel_left_of_respectsIso f.hom _).mp hrep)



end DoubledAffineLine

end AlgebraicGeometry.AlgebraicSpace
