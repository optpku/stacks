/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Small Zariski site of an algebraic space

The small Zariski site of an algebraic space `F` is the category of open subspaces of
`F`, with covering families the Zariski coverings of those open subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The underlying category of the small Zariski site of an algebraic space: objects are open
immersions into `F`, and morphisms are triangles over `F`. -/
abbrev smallZariskiSite {S : Scheme.{u}} (F : AlgebraicSpace S) :=
  MorphismProperty.Over
    (fun {X Y : AlgebraicSpace S} (f : X ⟶ Y) ↦ IsOpenImmersion f) ⊤ F

/-- The structural morphism of an object of the small Zariski site of `F` is an open immersion
into `F`. -/
theorem isOpenImmersion_smallZariskiSite {S : Scheme.{u}} {F : AlgebraicSpace S}
    (U : smallZariskiSite F) : IsOpenImmersion U.hom :=
  U.prop

/-- The canonical forgetful functor from the small Zariski site of `F` to `Over F`. -/
abbrev smallZariskiForget {S : Scheme.{u}} (F : AlgebraicSpace S) :
    smallZariskiSite F ⥤ Over F :=
  MorphismProperty.Over.forget
    (fun {X Y : AlgebraicSpace S} (f : X ⟶ Y) ↦ IsOpenImmersion f) ⊤ F

/-- Forgetting the open-immersion condition on an object of the small Zariski site recovers the
underlying object of `Over F`. -/
theorem smallZariskiForget_obj {S : Scheme.{u}} {F : AlgebraicSpace S} (U : smallZariskiSite F) :
    (smallZariskiForget F).obj U = CategoryTheory.Over.mk U.hom :=
  rfl

/-- The canonical forgetful functor from the small Zariski site of `F` to algebraic spaces over
`S`. -/
abbrev smallZariskiToSpace {S : Scheme.{u}} (F : AlgebraicSpace S) :
    smallZariskiSite F ⥤ AlgebraicSpace S :=
  smallZariskiForget F ⋙ CategoryTheory.Over.forget F

/-- The underlying algebraic space of an open subspace is the domain of its structural open
immersion. -/
theorem smallZariskiToSpace_obj {S : Scheme.{u}} {F : AlgebraicSpace S} (U : smallZariskiSite F) :
    (smallZariskiToSpace F).obj U = U.left :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A morphism in the small Zariski site of `F` is an open immersion of algebraic spaces. -/
theorem isOpenImmersion_smallZariskiSite_map {S : Scheme.{u}} {F : AlgebraicSpace S}
    {U V : smallZariskiSite F} (f : U ⟶ V) : IsOpenImmersion f.left := by
  haveI : @Mono ((Over S)ᵒᵖ ⥤ Type u) _
      V.left.functorOfPoints F.functorOfPoints V.hom := by
    apply MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    apply MorphismProperty.relative_monotone (P :=
      MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion)) ?_ _ V.prop.presheaf
    intro A B g hg
    haveI : AlgebraicGeometry.IsOpenImmersion g.left := hg
    exact CategoryTheory.Over.mono_of_mono_left g
  exact ⟨(MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.over (@AlgebraicGeometry.IsOpenImmersion))).of_isPullback
      (IsPullback.of_horiz_isIso_mono (C := (Over S)ᵒᵖ ⥤ Type u)
        (fst := 𝟙 U.left.functorOfPoints)
        (snd := f.left) (f := (U.hom : U.left.functorOfPoints ⟶ F.functorOfPoints))
        (g := (V.hom : V.left.functorOfPoints ⟶ F.functorOfPoints))
        ⟨by
          change U.hom = f.left ≫ V.hom
          exact (MorphismProperty.Over.w f).symm⟩)
      U.prop.presheaf⟩

/-- The Zariski precoverage on open subspaces of `F`: covering presieves are those presented by
a small family whose underlying algebraic-space morphisms form a Zariski covering. -/
def smallZariskiPrecoverage {S : Scheme.{u}} (F : AlgebraicSpace S) :
    Precoverage (smallZariskiSite F) where
  coverings U :=
    { R | ∃ (I : Type u) (_ : Small.{u} I) (V : I → smallZariskiSite F) (f : ∀ i, V i ⟶ U),
        R = Presieve.ofArrows V f ∧
          IsZariskiCover U.left (fun i ↦ (V i).left) (fun i ↦ (f i).left) }

/-- A displayed family is a covering in the small Zariski precoverage of `F` if and only if the
coproduct of the underlying functors of points is locally surjective as fppf sheaves. -/
theorem ofArrows_mem_smallZariskiPrecoverage_iff {S : Scheme.{u}} {F : AlgebraicSpace S}
    {I : Type u} [Small.{u} I] {U : smallZariskiSite F} {V : I → smallZariskiSite F}
    {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ smallZariskiPrecoverage F U ↔
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (Sigma.desc fun i ↦ (f i).left) := by
  constructor
  · rintro ⟨K, hK, W, g, hR, hg⟩
    have hlift : ∀ {T : smallZariskiSite F} (a : T ⟶ U),
        Presieve.ofArrows V f a → ∀ (B : (Over S)ᵒᵖ)
          (t : T.left.functorOfPoints.obj B),
          ∃ y, (Sigma.desc (C := (Over S)ᵒᵖ ⥤ Type u)
            fun i ↦ (f i).left).app B y = a.left.app B t := by
      intro T a ha B t
      cases ha with
      | mk i =>
        exact ⟨(Sigma.ι (fun i ↦ (V i).left.functorOfPoints) i).app B t,
          ConcreteCategory.congr_hom
            (congr_app (Sigma.ι_desc (C := (Over S)ᵒᵖ ⥤ Type u)
              (fun i ↦ (f i).left) i) B) t⟩
    constructor
    intro T s
    refine (Scheme.fppfTopology.over S).superset_covering ?_ (hg.2.imageSieve_mem s)
    intro B a ha
    obtain ⟨z, hz⟩ := ha
    obtain ⟨⟨j⟩, t, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation ((Over S)ᵒᵖ) (Type u)).obj (Opposite.op B))
        (colimit.isColimit (Discrete.functor fun j ↦ (W j).left.functorOfPoints))) z
    obtain ⟨y, hy⟩ := hlift (g j) (hR.symm ▸ Presieve.ofArrows.mk j) (Opposite.op B) t
    refine ⟨y, hy.trans (?_ : (g j).left.app (Opposite.op B) t = _)⟩
    exact (ConcreteCategory.congr_hom
      (congr_app (Sigma.ι_desc (C := (Over S)ᵒᵖ ⥤ Type u)
        (fun j ↦ (g j).left) j) (Opposite.op B)) t).symm.trans hz
  · intro hf
    exact ⟨I, inferInstance, V, f, rfl,
      ⟨fun i ↦ (isOpenImmersion_smallZariskiSite_map (f i)).presheaf, hf⟩⟩

/-- A displayed family covers in the small Zariski site precisely when its underlying
family of algebraic spaces satisfies the canonical Zariski covering predicate. -/
theorem ofArrows_mem_smallZariskiPrecoverage_iff_isZariskiCover
    {S : Scheme.{u}} {F : AlgebraicSpace S} {I : Type u} [Small.{u} I]
    {U : smallZariskiSite F} {V : I → smallZariskiSite F} {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ smallZariskiPrecoverage F U ↔
      IsZariskiCover U.left (fun i ↦ (V i).left) (fun i ↦ (f i).left) := by
  rw [ofArrows_mem_smallZariskiPrecoverage_iff]
  exact ⟨fun h ↦ ⟨fun i ↦ (isOpenImmersion_smallZariskiSite_map (f i)).presheaf, h⟩,
    fun h ↦ h.2⟩

/-- The small Zariski topology of an algebraic space `F` is the Grothendieck topology generated
by Zariski covering families of open subspaces of `F`. -/
def smallZariskiTopology {S : Scheme.{u}} (F : AlgebraicSpace S) :
    GrothendieckTopology (smallZariskiSite F) :=
  (smallZariskiPrecoverage F).toGrothendieck

/-- The small Zariski topology is generated by its concrete precoverage. -/
theorem smallZariskiTopology_def {S : Scheme.{u}} (F : AlgebraicSpace S) :
    smallZariskiTopology F = (smallZariskiPrecoverage F).toGrothendieck :=
  rfl

/-- The four site axioms hold for the precoverage of open subspaces of an algebraic space. -/
theorem smallZariskiPrecoverage_site_axioms {S : Scheme.{u}} (F : AlgebraicSpace S) :
    let J := smallZariskiPrecoverage F
    J.HasIsos ∧ J.HasPullbacks ∧
      (∀ {U} {R : Presieve U}, R ∈ J U →
        ∀ (covers : ∀ ⦃V⦄ (arrow : V ⟶ U), R arrow → Presieve V),
          (∀ ⦃V⦄ (arrow : V ⟶ U) (member : R arrow),
            covers arrow member ∈ J V) → R.bind covers ∈ J U) ∧
      (∀ {U V} (arrow : V ⟶ U) {R : Presieve U} [R.HasPullbacks arrow],
        R ∈ J U → R.pullbackArrows arrow ∈ J V) := sorry

end AlgebraicGeometry.AlgebraicSpace
