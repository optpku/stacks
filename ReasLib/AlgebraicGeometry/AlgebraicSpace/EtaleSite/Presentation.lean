/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The chart presentation of the small étale site using étale maps of algebraic spaces. -/
abbrev smallEtaleSite {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  MorphismProperty.CostructuredArrow (@AlgebraicGeometry.AlgebraicSpace.Etale S) ⊤
    (ofOverFunctor S) X

/-- The constructor for a chart in the small étale site presentation. -/
def smallEtaleSite.mk {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (hφ : AlgebraicGeometry.AlgebraicSpace.Etale φ := by infer_instance) :
    smallEtaleSite X :=
  MorphismProperty.CostructuredArrow.mk ⊤ φ hφ

/-- The underlying scheme over `S` of a constructed étale chart. -/
@[simp]
theorem smallEtaleSite.mk_left {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (hφ : AlgebraicGeometry.AlgebraicSpace.Etale φ := by infer_instance) :
    (smallEtaleSite.mk φ hφ).left = U := rfl

/-- The structural morphism of a constructed étale chart. -/
@[simp]
theorem smallEtaleSite.mk_hom {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (hφ : AlgebraicGeometry.AlgebraicSpace.Etale φ := by infer_instance) :
    (smallEtaleSite.mk φ hφ).hom = φ := rfl

/-- The structural morphism of a chart is étale. -/
instance etale_hom {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    AlgebraicGeometry.AlgebraicSpace.Etale U.hom := U.prop

/-- The commuting triangle equation of a chart morphism. -/
theorem smallEtaleSite.w {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (f : U ⟶ V) :
    (ofOverFunctor S).map f.left ≫ V.hom = U.hom := f.w

/-- The projection from the chart presentation to schemes over the base. -/
def smallEtaleToOver {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite X ⥤ Over S where
  obj U := U.left
  map f := f.left
  map_id := by intro U; rfl
  map_comp := by intro U V W f g; rfl

/-- The object map of the chart-to-over projection. -/
theorem smallEtaleToOver_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X) : (smallEtaleToOver X).obj U = U.left := rfl

/-- The morphism map of the chart-to-over projection. -/
theorem smallEtaleToOver_map {S : Scheme.{u}} (X : AlgebraicSpace S)
    {U V : smallEtaleSite X} (f : U ⟶ V) : (smallEtaleToOver X).map f = f.left := rfl

/-- The underlying scheme functor on the chart presentation. -/
def smallEtaleToScheme {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite X ⥤ Scheme.{u} := smallEtaleToOver X ⋙ Over.forget S

/-- The scheme underlying the chart-to-scheme projection is the chart's underlying scheme. -/
theorem smallEtaleToScheme_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : smallEtaleSite X) : (smallEtaleToScheme X).obj U = U.left.left := rfl

namespace smallEtaleSite

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

set_option backward.isDefEq.respectTransparency false in
theorem etale_precomp {U V : Over S} (g : U ⟶ V) [AlgebraicGeometry.Etale g.left]
    (a : AlgebraicSpace.ofOver V ⟶ X) [AlgebraicSpace.Etale a] :
    AlgebraicSpace.Etale ((AlgebraicSpace.ofOverFunctor S).map g ≫ a) := by
  letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
      MorphismProperty (Over S)).IsStableUnderComposition := by
    rw [MorphismProperty.over_eq_inverseImage]
    infer_instance
  letI : (MorphismProperty.over (@AlgebraicGeometry.Etale) :
      MorphismProperty (Over S)).IsStableUnderBaseChange :=
    ⟨fun square etaleMap ↦ MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      (square.map (Over.forget S)) etaleMap⟩
  have hmap : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
      (yoneda.map g) := MorphismProperty.relative_map (F := yoneda) ‹AlgebraicGeometry.Etale g.left›
  exact ⟨fun testMap testEtale ↦
    (inferInstance : AlgebraicSpace.Etale a).of_etale _
      ((MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf.comp_mem _ _ testEtale hmap)⟩

variable {V T W : AlgebraicSpace.smallEtaleSite X} (f : V ⟶ W) (g : T ⟶ W)
  [AlgebraicGeometry.Etale g.left.left]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback chart uses the actual pullback in `Over S`. -/
def pullbackConeOfEtale : PullbackCone f g := by
  let p := pullback f.left g.left
  let fstMap := pullback.fst f.left g.left
  let sndMap := pullback.snd f.left g.left
  letI : AlgebraicGeometry.Etale fstMap.left :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale)
      ((IsPullback.of_hasPullback f.left g.left).map (Over.forget S)).flip
      (inferInstance : AlgebraicGeometry.Etale g.left.left)
  letI : AlgebraicSpace.Etale V.hom := V.prop
  let chart := AlgebraicSpace.smallEtaleSite.mk
    ((AlgebraicSpace.ofOverFunctor S).map fstMap ≫ V.hom) (etale_precomp fstMap V.hom)
  let firstMap : chart ⟶ V := MorphismProperty.CostructuredArrow.homMk fstMap trivial rfl
  let secondMap : chart ⟶ T := MorphismProperty.CostructuredArrow.homMk sndMap trivial (by
    have fw : yoneda.map f.left ≫ W.hom = V.hom := f.w
    have gw : yoneda.map g.left ≫ W.hom = T.hom := g.w
    change yoneda.map sndMap ≫ T.hom = yoneda.map fstMap ≫ V.hom
    rw [← gw, ← fw, ← Category.assoc, ← Category.assoc,
      ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition])
  exact PullbackCone.mk firstMap secondMap (by
    exact MorphismProperty.CostructuredArrow.Hom.ext (pullback.condition (f := f.left) (g := g.left)))

set_option backward.isDefEq.respectTransparency false in
/-- The lift is the actual underlying pullback lift, with the chart triangle. -/
def pullbackConeOfEtaleIsLimit : IsLimit (pullbackConeOfEtale f g) := by
  refine PullbackCone.IsLimit.mk (pullbackConeOfEtale f g).condition (fun c ↦ ?_) ?_ ?_ ?_
  · exact MorphismProperty.CostructuredArrow.homMk
      (pullback.lift c.fst.left c.snd.left
        (congrArg (fun k ↦ k.left) c.condition)) trivial (by
          change yoneda.map (pullback.lift _ _ _) ≫
            (yoneda.map (pullback.fst f.left g.left) ≫ V.hom) = c.pt.hom
          rw [← Category.assoc, ← yoneda.map_comp, pullback.lift_fst]
          exact c.fst.w)
  · intro c
    exact MorphismProperty.CostructuredArrow.Hom.ext (pullback.lift_fst _ _ _)
  · intro c
    exact MorphismProperty.CostructuredArrow.Hom.ext (pullback.lift_snd _ _ _)
  · intro c m firstEquality secondEquality
    apply MorphismProperty.CostructuredArrow.Hom.ext
    apply pullback.hom_ext
    · exact (congrArg (fun k ↦ k.left) firstEquality).trans
        (pullback.lift_fst (f := f.left) (g := g.left) c.fst.left c.snd.left
          (congrArg (fun k ↦ k.left) c.condition)).symm
    · exact (congrArg (fun k ↦ k.left) secondEquality).trans
        (pullback.lift_snd (f := f.left) (g := g.left) c.fst.left c.snd.left
          (congrArg (fun k ↦ k.left) c.condition)).symm

set_option backward.isDefEq.respectTransparency false in
theorem preservesPullback_toOver_of_etale : PreservesLimit (cospan f g) (AlgebraicSpace.smallEtaleToOver X) := by
  apply preservesLimit_of_preserves_limit_cone (pullbackConeOfEtaleIsLimit f g)
  refine (PullbackCone.isLimitMapConeEquiv (pullbackConeOfEtale f g) _).symm ?_
  exact IsLimit.ofIsoLimit (pullback.isLimit f.left g.left)
    (PullbackCone.ext (Iso.refl _) (by rfl) (by rfl))


set_option backward.isDefEq.respectTransparency false in
theorem preservesPullback_toScheme_of_etale : PreservesLimit (cospan f g) (AlgebraicSpace.smallEtaleToScheme X) := by
  letI := preservesPullback_toOver_of_etale f g
  dsimp only [AlgebraicSpace.smallEtaleToScheme]
  infer_instance

@[simp] theorem pullbackConeOfEtale_fst_left :
    (pullbackConeOfEtale f g).fst.left = pullback.fst f.left g.left := rfl

@[simp] theorem pullbackConeOfEtale_snd_left :
    (pullbackConeOfEtale f g).snd.left = pullback.snd f.left g.left := rfl

end smallEtaleSite

/-- The chart presentation's precoverage is the comap of the scheme étale precoverage. -/
def smallEtalePrecoverage {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Precoverage (smallEtaleSite X) :=
  (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).toPrecoverage.comap
    (smallEtaleToOver X)

/-- A displayed chart family belongs to the presentation precoverage exactly when its image
family belongs to the étale precoverage over `S`. -/
theorem ofArrows_mem_smallEtalePrecoverage_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type u} [Small.{u} I] {U : smallEtaleSite X} {V : I → smallEtaleSite X}
    {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ (smallEtalePrecoverage X).coverings U ↔
      Presieve.ofArrows (fun i => (smallEtaleToOver X).obj (V i))
        (fun i => (smallEtaleToOver X).map (f i)) ∈
        (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).toPrecoverage.coverings
          ((smallEtaleToOver X).obj U) := by
  simp only [smallEtalePrecoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]

/-- The Grothendieck topology generated by the chart presentation's precoverage. -/
def smallEtaleTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    GrothendieckTopology (smallEtaleSite X) := (smallEtalePrecoverage X).toGrothendieck

/-- The generated topology is the Grothendieck topology associated to the presentation
precoverage. -/
theorem smallEtaleTopology_def {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleTopology X = (smallEtalePrecoverage X).toGrothendieck := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restricting an étale sheaf along the chart projection preserves its sheaf condition.
The auxiliary scheme-induced precoverage is used only to prove continuity; the original
chart topology is retained. -/
theorem smallEtaleToScheme_isContinuous {S : Scheme.{u}} (X : AlgebraicSpace S) : (AlgebraicSpace.smallEtaleToScheme X).IsContinuous
    (AlgebraicSpace.smallEtaleTopology X) Scheme.etaleTopology := by
  let F := AlgebraicSpace.smallEtaleToScheme X
  let J := (Scheme.precoverage (@AlgebraicGeometry.Etale)).comap F
  have arrowEtale {Z Y : AlgebraicSpace.smallEtaleSite X} {R : Presieve Z}
      (hR : R ∈ J Z) {g : Y ⟶ Z} (hg : R g) : AlgebraicGeometry.Etale g.left.left :=
    hR.2 (Presieve.map_map hg)
  letI : J.HasPullbacks := ⟨fun f hR ↦ ⟨fun {T g} hg ↦ by
    letI := arrowEtale hR hg
    have : HasPullback f g := ⟨⟨smallEtaleSite.pullbackConeOfEtale f g, smallEtaleSite.pullbackConeOfEtaleIsLimit f g⟩⟩
    exact hasPullback_symmetry f g⟩⟩
  letI : J.IsStableUnderBaseChange := by
    constructor
    intro ι W familyObjects family hR Y baseMap PB p₁ p₂ squares
    change (Presieve.ofArrows _ p₁).map F ∈ Scheme.precoverage (@AlgebraicGeometry.Etale) _
    rw [Presieve.map_ofArrows]
    apply Precoverage.mem_coverings_of_isPullback (fun i ↦ F.map (family i))
      (by simpa only [J, Precoverage.mem_comap_iff, Presieve.map_ofArrows] using hR) (F.map baseMap)
      (fun i ↦ F.map (p₁ i)) (fun i ↦ F.map (p₂ i))
    intro i
    letI := arrowEtale hR (Presieve.ofArrows.mk i)
    letI := smallEtaleSite.preservesPullback_toScheme_of_etale baseMap (family i)
    exact (squares i).map F
  letI : J.PullbacksPreservedBy F := by
    constructor
    intro Z R hR
    constructor
    intro Y T f g hf hg
    letI := arrowEtale hR hg
    exact smallEtaleSite.preservesPullback_toScheme_of_etale f g
  letI : F.IsContinuous J.toGrothendieck Scheme.etaleTopology :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy F J
      (Scheme.precoverage (@AlgebraicGeometry.Etale)) le_rfl
  have inclusion : AlgebraicSpace.smallEtalePrecoverage X ≤ J := by
    change (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).toPrecoverage.comap
      (AlgebraicSpace.smallEtaleToOver X) ≤
      (Scheme.precoverage (@AlgebraicGeometry.Etale)).comap
        (AlgebraicSpace.smallEtaleToOver X ⋙ Over.forget S)
    rw [Precoverage.comap_comp]
    apply Precoverage.comap_monotone
    intro Z R hR
    obtain ⟨cover, coverOver, rfl⟩ := hR
    letI := coverOver
    change cover.toPresieveOver.map (Over.forget S) ∈ Scheme.precoverage (@AlgebraicGeometry.Etale) _
    rw [Scheme.Cover.toPresieveOver, Presieve.map_ofArrows]
    exact cover.mem₀
  constructor
  intro G
  exact Presieve.isSheaf_of_le _ (Precoverage.toGrothendieck_mono inclusion)
    (F.op_comp_isSheaf_of_types J.toGrothendieck Scheme.etaleTopology G)


/-- The presentation precoverage contains singleton isomorphism covers. -/
instance smallEtalePrecoverage.instHasIsos {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtalePrecoverage X).HasIsos := by
  constructor
  intro U V f hf
  change (Presieve.singleton f).map (smallEtaleToOver X) ∈
    (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).coverings _
  rw [Presieve.map_singleton]
  exact (Scheme.overPretopology (@AlgebraicGeometry.Etale) S).has_isos
    ((smallEtaleToOver X).map f)

/-- A covering arrow has an étale underlying scheme map. -/
theorem smallEtalePrecoverage.etale_of_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Z Y : smallEtaleSite X} {R : Presieve Z}
    (hR : R ∈ smallEtalePrecoverage X Z) {g : Y ⟶ Z} (hg : R g) :
    AlgebraicGeometry.Etale g.left.left := by
  obtain ⟨cover, coverOver, coverEquality⟩ := hR
  letI := coverOver
  have imageMem := Presieve.map_map (F := smallEtaleToOver X) hg
  rw [coverEquality] at imageMem
  have etaleArrow {A : Over S} (k : A ⟶ Z.left) (hk : cover.toPresieveOver k) :
      AlgebraicGeometry.Etale k.left := by
    cases hk with
    | mk index => exact cover.map_prop index
  exact etaleArrow g.left imageMem

/-- Pullbacks of arrows in a covering presieve exist in the presentation. -/
theorem smallEtalePrecoverage.hasPullbacks_of_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y Z : smallEtaleSite X} {R : Presieve Z} (f : Y ⟶ Z)
    (hR : R ∈ (smallEtalePrecoverage X).coverings Z) : R.HasPullbacks f := by
  constructor
  intro T g hg
  letI := smallEtalePrecoverage.etale_of_mem hR hg
  have : HasPullback f g :=
    ⟨⟨smallEtaleSite.pullbackConeOfEtale f g, smallEtaleSite.pullbackConeOfEtaleIsLimit f g⟩⟩
  exact hasPullback_symmetry f g

/-- The presentation precoverage has pullbacks for all covering presieves. -/
instance smallEtalePrecoverage.instHasPullbacks {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtalePrecoverage X).HasPullbacks :=
  ⟨smallEtalePrecoverage.hasPullbacks_of_mem⟩

/-- The presentation precoverage is stable under binding covering families. -/
theorem smallEtalePrecoverage.bind_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : smallEtaleSite X} {R : Presieve U}
    (hR : R ∈ (smallEtalePrecoverage X).coverings U)
    (T : ⦃V : smallEtaleSite X⦄ → (f : V ⟶ U) → R f → Presieve V)
    (hT : ∀ ⦃V : smallEtaleSite X⦄ (f : V ⟶ U) (hf : R f),
      T f hf ∈ (smallEtalePrecoverage X).coverings V) :
    R.bind T ∈ (smallEtalePrecoverage X).coverings U := sorry

/-- Pulling back a covering presieve gives a covering presieve in the presentation. -/
theorem smallEtalePrecoverage.pullbackArrows_mem {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (f : V ⟶ U) {R : Presieve U}
    [R.HasPullbacks f] (hR : R ∈ (smallEtalePrecoverage X).coverings U) :
    Presieve.pullbackArrows f R ∈ (smallEtalePrecoverage X).coverings V := sorry

/-- Étaleness of a map from a representable algebraic space agrees with representable étaleness. -/
theorem SmallEtale.etale_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) :
    AlgebraicGeometry.AlgebraicSpace.Etale φ ↔ Representable.Etale φ := sorry

/-- The forward functor from the chart presentation to the canonical site. -/
def SmallEtale.fromPresentation {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallEtaleSite X ⥤ SmallEtale.site X where
  obj U := MorphismProperty.CostructuredArrow.mk ⊤ U.hom
    ((SmallEtale.etale_iff U.hom).mp U.prop)
  map f := MorphismProperty.CostructuredArrow.homMk f.left trivial f.w
  map_id := fun _ => MorphismProperty.CostructuredArrow.Hom.ext rfl
  map_comp := fun _ _ => MorphismProperty.CostructuredArrow.Hom.ext rfl

/-- The reverse functor from the canonical site to the chart presentation. -/
def SmallEtale.toPresentation {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.site X ⥤ smallEtaleSite X where
  obj U := MorphismProperty.CostructuredArrow.mk ⊤ U.hom
    ((SmallEtale.etale_iff U.hom).mpr U.prop)
  map f := MorphismProperty.CostructuredArrow.homMk f.left trivial f.w
  map_id := fun _ => MorphismProperty.CostructuredArrow.Hom.ext rfl
  map_comp := fun _ _ => MorphismProperty.CostructuredArrow.Hom.ext rfl

/-- The forward chart comparison preserves the underlying scheme over the base. -/
@[simp]
theorem SmallEtale.fromPresentation_obj_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) : ((SmallEtale.fromPresentation X).obj U).left = U.left := rfl

/-- The forward chart comparison preserves the structural map. -/
@[simp]
theorem SmallEtale.fromPresentation_obj_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) : ((SmallEtale.fromPresentation X).obj U).hom = U.hom := rfl

/-- The forward chart comparison preserves the underlying scheme morphism. -/
@[simp]
theorem SmallEtale.fromPresentation_map_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallEtaleSite X} (g : U ⟶ V) :
    ((SmallEtale.fromPresentation X).map g).left = g.left := rfl

/-- The reverse chart comparison preserves the underlying scheme over the base. -/
@[simp]
theorem SmallEtale.toPresentation_obj_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : SmallEtale.site X) : ((SmallEtale.toPresentation X).obj U).left = U.left := rfl

/-- The reverse chart comparison preserves the structural map. -/
@[simp]
theorem SmallEtale.toPresentation_obj_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : SmallEtale.site X) : ((SmallEtale.toPresentation X).obj U).hom = U.hom := rfl

/-- The reverse chart comparison preserves the underlying scheme morphism. -/
@[simp]
theorem SmallEtale.toPresentation_map_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : SmallEtale.site X} (g : U ⟶ V) :
    ((SmallEtale.toPresentation X).map g).left = g.left := rfl

/-- Converting a canonical-site chart to the presentation and back recovers the chart. -/
@[simp]
theorem SmallEtale.fromPresentation_obj_toPresentation_obj {S : Scheme.{u}}
    {X : AlgebraicSpace S} (U : SmallEtale.site X) :
    (SmallEtale.fromPresentation X).obj ((SmallEtale.toPresentation X).obj U) = U := rfl

/-- Converting a presentation chart to the canonical site and back recovers the chart. -/
@[simp]
theorem SmallEtale.toPresentation_obj_fromPresentation_obj {S : Scheme.{u}}
    {X : AlgebraicSpace S} (U : smallEtaleSite X) :
    (SmallEtale.toPresentation X).obj ((SmallEtale.fromPresentation X).obj U) = U := rfl

/-- The chart-presentation round trip is the identity functor. -/
theorem SmallEtale.fromPresentation_toPresentation {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.fromPresentation X ⋙ SmallEtale.toPresentation X = 𝟭 (smallEtaleSite X) := sorry

/-- The canonical-site round trip is the identity functor. -/
theorem SmallEtale.toPresentation_fromPresentation {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.toPresentation X ⋙ SmallEtale.fromPresentation X = 𝟭 (SmallEtale.site X) := sorry

/-- The forward comparison preserves the chart-to-over projection. -/
theorem SmallEtale.fromPresentation_toOver {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.fromPresentation X ⋙ SmallEtale.toOver X = smallEtaleToOver X := sorry

/-- The reverse comparison preserves the chart-to-over projection. -/
theorem SmallEtale.toPresentation_toOver {S : Scheme.{u}} (X : AlgebraicSpace S) :
    SmallEtale.toPresentation X ⋙ smallEtaleToOver X = SmallEtale.toOver X := sorry

/-- The forward comparison identifies covering chart families. -/
theorem SmallEtale.fromPresentation_cover_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type u} [Small.{u} I] {U : smallEtaleSite X} {V : I → smallEtaleSite X}
    {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ (smallEtalePrecoverage X).coverings U ↔
      Presieve.ofArrows (fun i => (SmallEtale.fromPresentation X).obj (V i))
        (fun i => (SmallEtale.fromPresentation X).map (f i)) ∈
        (SmallEtale.precoverage X).coverings ((SmallEtale.fromPresentation X).obj U) := sorry

/-- The reverse comparison identifies covering canonical-site families. -/
theorem SmallEtale.toPresentation_cover_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type u} [Small.{u} I] {U : SmallEtale.site X} {V : I → SmallEtale.site X}
    {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ (SmallEtale.precoverage X).coverings U ↔
      Presieve.ofArrows (fun i => (SmallEtale.toPresentation X).obj (V i))
        (fun i => (SmallEtale.toPresentation X).map (f i)) ∈
        (smallEtalePrecoverage X).coverings ((SmallEtale.toPresentation X).obj U) := sorry

/-- The forward comparison identifies the generated covering sieves. -/
theorem SmallEtale.fromPresentation_topology_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : smallEtaleSite X} (R : Sieve U) :
    R ∈ smallEtaleTopology X U ↔
      Sieve.functorPushforward (SmallEtale.fromPresentation X) R ∈
        SmallEtale.topology X ((SmallEtale.fromPresentation X).obj U) := sorry

end AlgebraicGeometry.AlgebraicSpace
