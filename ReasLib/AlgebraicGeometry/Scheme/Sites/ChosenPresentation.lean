/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Pretopology
public import ReasLib.AlgebraicGeometry.Scheme.Size
public import ReasLib.AlgebraicGeometry.Scheme.VonNeumann
public import ReasLib.SetTheory.Cardinal.Bound
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Map
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Equivalence
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over

/-!
# Chosen presentations of big scheme sites

A chosen presentation records a small category of schemes, selected objects and
covering families, and a pretopology whose coverings are represented by covers
for a fixed precoverage on schemes.

These local laws are also useful without the object closure of a big site.
`SchAlphaBigSite` adds an explicit comparison with the category `Sch_α` of
Stacks, Tag 000J; it is the presentation used by the Chapter 34 definitions.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The laws relating selected objects and covering families in a small category
of schemes to a precoverage on schemes. -/
structure IsChosenBigSite (P : Precoverage Scheme.{u}) (carrier : Cat.{u, v})
    (hasPullbacks : Limits.HasPullbacks carrier) (toScheme : Functor carrier Scheme.{u})
    (seedSchemes : Set carrier) (seedCoverings : ∀ X : carrier, Set (Presieve X))
    (pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks) : Prop where
  /-- The functor to schemes preserves pullbacks. -/
  toScheme_preservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan toScheme
  /-- The target of every selected covering family is selected. -/
  seedCovering_target_mem :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X → X ∈ seedSchemes
  /-- The source of every arrow in a selected covering family is selected. -/
  seedCovering_source_mem :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X →
      ∀ {Y : carrier} (f : Y ⟶ X), R f → Y ∈ seedSchemes
  /-- Every selected covering family belongs to the pretopology. -/
  seedCoverings_le :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X → R ∈ pretopology X
  /-- Every selected covering family is represented, after applying the scheme
functor, by a cover for the ambient precoverage. -/
  seedCovering_exists_cover :
    ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X →
      ∃ 𝒰 : Scheme.Cover.{u} P (toScheme.obj X),
        R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f
  /-- Every covering family in the pretopology is represented, after applying
the scheme functor, by a cover for the ambient precoverage. -/
  covering_exists_cover :
    ∀ {X : carrier} {R : Presieve X}, R ∈ pretopology X →
      ∃ 𝒰 : Scheme.Cover.{u} P (toScheme.obj X),
        R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f
  /-- Bounded-size schemes have representatives, as in Stacks, Tag 000J.
  This does not require representing every source of an arbitrary ambient cover. -/
  boundedObject_exists_iso :
    ∀ (X : carrier) (T : Scheme.{u}),
      T.size ≤ Cardinal.countableSuccBound (toScheme.obj X).size →
        ∃ Y : carrier, Nonempty (toScheme.obj Y ≅ T)
  /-- A family in the chosen carrier covers whenever its image is
  tautologically equivalent to an ambient cover. -/
  isCovering_of_tautologicallyEquivalent :
    ∀ {X : carrier} (𝒰 : Scheme.Cover.{u} P (toScheme.obj X))
      (𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over X)),
      Limits.FormalCoproduct.TautologicallyEquivalent
          ((Limits.FormalCoproduct.map
            (CategoryTheory.Over.post (X := X) toScheme)).obj 𝒱)
          (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f) →
        𝒱.toPresieve ∈ pretopology.toPrecoverage X
  /-- Arbitrary ambient covers admit covering refinements in the carrier.
  This is the pro-étale interface of Stacks, Tag 098J, and does not assert
  representability of every ambient cover source. -/
  covering_exists_refinement :
    ∀ {X : carrier} (𝒰 : Scheme.Cover.{u} P (toScheme.obj X)),
      ∃ 𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over X),
        𝒱.toPresieve ∈ pretopology.toPrecoverage X ∧
          Nonempty (Limits.FormalCoproduct.Hom
            ((Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := X) toScheme)).obj 𝒱)
            (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f))

/-- Construct the laws of a chosen big-site presentation from preservation of
pullbacks, seed conditions, representations of covering families, and the
tautological covering condition. -/
def IsChosenBigSite.of {P : Precoverage Scheme.{u}} {carrier : Cat.{u, v}}
    {hasPullbacks : Limits.HasPullbacks carrier} {toScheme : Functor carrier Scheme.{u}}
    {seedSchemes : Set carrier} {seedCoverings : ∀ X : carrier, Set (Presieve X)}
    {pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks}
    (toScheme_preservesPullbacks :
      Limits.PreservesLimitsOfShape Limits.WalkingCospan toScheme)
    (seedCovering_target_mem :
      ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X → X ∈ seedSchemes)
    (seedCovering_source_mem :
      ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X →
        ∀ {Y : carrier} (f : Y ⟶ X), R f → Y ∈ seedSchemes)
    (seedCoverings_le :
      ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X → R ∈ pretopology X)
    (seedCovering_exists_cover :
      ∀ {X : carrier} {R : Presieve X}, R ∈ seedCoverings X →
        ∃ 𝒰 : Scheme.Cover.{u} P (toScheme.obj X),
          R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f)
    (covering_exists_cover :
      ∀ {X : carrier} {R : Presieve X}, R ∈ pretopology X →
        ∃ 𝒰 : Scheme.Cover.{u} P (toScheme.obj X),
          R.map toScheme = Presieve.ofArrows 𝒰.X 𝒰.f)
    (boundedObject_exists_iso :
      ∀ (X : carrier) (T : Scheme.{u}),
        T.size ≤ Cardinal.countableSuccBound (toScheme.obj X).size →
          ∃ Y : carrier, Nonempty (toScheme.obj Y ≅ T))
    (isCovering_of_tautologicallyEquivalent :
      ∀ {X : carrier} (𝒰 : Scheme.Cover.{u} P (toScheme.obj X))
        (𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over X)),
        Limits.FormalCoproduct.TautologicallyEquivalent
            ((Limits.FormalCoproduct.map
              (CategoryTheory.Over.post (X := X) toScheme)).obj 𝒱)
            (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f) →
          𝒱.toPresieve ∈ pretopology.toPrecoverage X)
    (covering_exists_refinement :
      ∀ {X : carrier} (𝒰 : Scheme.Cover.{u} P (toScheme.obj X)),
        ∃ 𝒱 : Limits.FormalCoproduct.{u} (CategoryTheory.Over X),
          𝒱.toPresieve ∈ pretopology.toPrecoverage X ∧
            Nonempty (Limits.FormalCoproduct.Hom
              ((Limits.FormalCoproduct.map
                (CategoryTheory.Over.post (X := X) toScheme)).obj 𝒱)
              (Limits.FormalCoproduct.ofArrows 𝒰.X 𝒰.f))) :
    IsChosenBigSite P carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology where
  toScheme_preservesPullbacks := toScheme_preservesPullbacks
  seedCovering_target_mem := seedCovering_target_mem
  seedCovering_source_mem := seedCovering_source_mem
  seedCoverings_le := seedCoverings_le
  seedCovering_exists_cover := seedCovering_exists_cover
  covering_exists_cover := covering_exists_cover
  boundedObject_exists_iso := boundedObject_exists_iso
  isCovering_of_tautologicallyEquivalent := isCovering_of_tautologicallyEquivalent
  covering_exists_refinement := covering_exists_refinement

/-- Only cover sources within the object bound are automatically represented.
Arbitrary pro-étale covers instead admit covering refinements in a bounded site. -/
theorem IsChosenBigSite.coverSource_exists_iso
    {P : Precoverage Scheme.{u}} {carrier : Cat.{u, v}}
    {hasPullbacks : Limits.HasPullbacks carrier} {toScheme : carrier ⥤ Scheme.{u}}
    {seedSchemes : Set carrier} {seedCoverings : ∀ X : carrier, Set (Presieve X)}
    {pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks}
    (h : IsChosenBigSite P carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology)
    {X : carrier} (𝒰 : Scheme.Cover.{u} P (toScheme.obj X)) (i : 𝒰.I₀)
    (hsize : (𝒰.X i).size ≤ Cardinal.countableSuccBound (toScheme.obj X).size) :
    ∃ Y : carrier, Nonempty (toScheme.obj Y ≅ 𝒰.X i) :=
  h.boundedObject_exists_iso X (𝒰.X i) hsize

/-- A property of a covering class whose individual cover sources all satisfy
the ordinary big-site size bound. Zariski coverings satisfy this property;
arbitrary étale and pro-étale coverings do not. -/
class Scheme.HasBoundedCoverSources (P : Precoverage Scheme.{u}) : Prop where
  source_size_le_bound :
    ∀ {T : Scheme.{u}} (𝒰 : Scheme.Cover.{u} P T) (i : 𝒰.I₀),
      (𝒰.X i).size ≤ Cardinal.countableSuccBound T.size

/-- Local presentation data for a scheme precoverage. To present a big site in
the sense of Stacks, Tag 000J, use the anchored extension `SchAlphaBigSite`. -/
structure ChosenBigSite (P : Precoverage Scheme.{u}) where
  /-- The selected small category. -/
  carrier : Cat.{u, v}
  /-- A proof that the selected category has pullbacks. -/
  hasPullbacks : Limits.HasPullbacks carrier
  /-- The functor exhibiting the selected category as a category of schemes. -/
  toScheme : Functor carrier Scheme.{u}
  /-- The scheme functor is fully faithful. -/
  fullyFaithful : toScheme.FullyFaithful
  /-- The selected objects of the presentation. -/
  seedSchemes : Set carrier
  /-- The selected covering families of the presentation. -/
  seedCoverings : ∀ X : carrier, Set (Presieve X)
  /-- The pretopology on the selected category. -/
  pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks
  /-- The selected objects, covering families, and pretopology represent the
ambient scheme precoverage. -/
  specification :
    IsChosenBigSite P carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology

namespace ChosenBigSite

variable {P : Precoverage Scheme.{u}}

/-- Construct a chosen big-site presentation from explicit carrier, functor,
seed, pretopology, and specification data. -/
def ofPretopology (carrier : Cat.{u, v}) (hasPullbacks : Limits.HasPullbacks carrier)
    (toScheme : Functor carrier Scheme.{u}) (fullyFaithful : toScheme.FullyFaithful)
    (seedSchemes : Set carrier) (seedCoverings : ∀ X : carrier, Set (Presieve X))
    (pretopology : @Pretopology carrier (Cat.str carrier) hasPullbacks)
    (specification :
      IsChosenBigSite P carrier hasPullbacks toScheme seedSchemes seedCoverings pretopology) :
    ChosenBigSite P where
  carrier := carrier
  hasPullbacks := hasPullbacks
  toScheme := toScheme
  fullyFaithful := fullyFaithful
  seedSchemes := seedSchemes
  seedCoverings := seedCoverings
  pretopology := pretopology
  specification := specification

/-- The complete specification satisfied by a chosen big-site presentation. -/
theorem spec (X : ChosenBigSite P) :
    IsChosenBigSite P X.carrier X.hasPullbacks X.toScheme X.seedSchemes
      X.seedCoverings X.pretopology :=
  X.specification

/-- The Grothendieck topology generated by the pretopology of a chosen
big-site presentation. -/
def toGrothendieck (X : ChosenBigSite P) : GrothendieckTopology X.carrier :=
  @Pretopology.toGrothendieck X.carrier (Cat.str X.carrier) X.hasPullbacks X.pretopology

end ChosenBigSite

/-- Local presentation data for the Zariski precoverage. The source-facing
big-site definition is `SchAlphaBigSite Scheme.zariskiPrecoverage`. -/
abbrev ChosenBigZariskiSite : Type (max (u + 1) (v + 1)) :=
  ChosenBigSite.{u, v} Scheme.zariskiPrecoverage

namespace Scheme

/-- An explicit comparison with the native `Sch_α` category. The natural
isomorphism makes the comparison respect the underlying schemes. -/
structure SchAlphaPresentation (C : Cat.{u, v}) (F : C ⥤ Scheme.{u}) where
  /-- The level of the von Neumann hierarchy. -/
  ordinal : Ordinal.{u}
  /-- The comparison with the full category of schemes at this level. -/
  equivalence : C ≌ (vonNeumannStage ordinal).FullSubcategory
  /-- The comparison agrees with the scheme functor. -/
  toSchemeIso : equivalence.functor ⋙ (vonNeumannStage ordinal).ι ≅ F

/-- The level in a comparison is one supplied by Stacks, Tag 000J. The existing
closure predicate includes empty diagrams and all countable diagrams, with
countable object and morphism sets. -/
def SchAlphaPresentation.IsValid {C : Cat.{u, v}} {F : C ⥤ Scheme.{u}}
    (M : SchAlphaPresentation C F) : Prop :=
  Order.IsSuccLimit M.ordinal ∧ IsSmallBoundClosed (vonNeumannStage M.ordinal)

namespace SchAlphaPresentation

/-- Existence of countable limits is detected in schemes through the actual
`Sch_α` comparison. This includes the empty diagram. -/
theorem hasLimit_iff {C : Cat.{u, v}} {F : C ⥤ Scheme.{u}}
    (M : SchAlphaPresentation C F) (hM : M.IsValid)
    {J : Type} [SmallCategory J] [CountableCategory J] (K : J ⥤ C) :
    Limits.HasLimit K ↔ Limits.HasLimit (K ⋙ F) := by
  have hK : Limits.HasLimit K ↔ Limits.HasLimit (K ⋙ M.equivalence.functor) :=
    ⟨fun _ ↦ Adjunction.hasLimit_comp_equivalence K M.equivalence.functor,
      fun _ ↦ Adjunction.hasLimit_of_comp_equivalence K M.equivalence.functor⟩
  exact hK.trans ((hM.2.hasLimit_iff _).trans
    (Limits.hasLimit_iff_of_iso
      (Functor.associator K M.equivalence.functor _ ≪≫
        Functor.isoWhiskerLeft K M.toSchemeIso)))

/-- Existence of countable colimits is detected in schemes through the actual
`Sch_α` comparison. This includes the empty diagram. -/
theorem hasColimit_iff {C : Cat.{u, v}} {F : C ⥤ Scheme.{u}}
    (M : SchAlphaPresentation C F) (hM : M.IsValid)
    {J : Type} [SmallCategory J] [CountableCategory J] (K : J ⥤ C) :
    Limits.HasColimit K ↔ Limits.HasColimit (K ⋙ F) := by
  have hK : Limits.HasColimit K ↔ Limits.HasColimit (K ⋙ M.equivalence.functor) :=
    ⟨fun _ ↦ Adjunction.hasColimit_comp_equivalence K M.equivalence.functor,
      fun _ ↦ Adjunction.hasColimit_of_comp_equivalence K M.equivalence.functor⟩
  exact hK.trans ((hM.2.hasColimit_iff _).trans
    (Limits.hasColimit_iff_of_iso
      (Functor.associator K M.equivalence.functor _ ≪≫
        Functor.isoWhiskerLeft K M.toSchemeIso)))

/-- The comparison with schemes preserves countable limits when they exist. -/
theorem preservesLimitsOfShape {C : Cat.{u, v}} {F : C ⥤ Scheme.{u}}
    (M : SchAlphaPresentation C F) (hM : M.IsValid)
    (J : Type) [SmallCategory J] [CountableCategory J] :
    Limits.PreservesLimitsOfShape J F := by
  letI : Limits.PreservesLimitsOfShape J (vonNeumannStage M.ordinal).ι := {
    preservesLimit := fun {K} ↦ Limits.PreservesLimit.mk' fun hK ↦ by
      letI := hK
      haveI := (hM.2.hasLimit_iff K).mp hK
      haveI := hM.2.isIso_limit_post K
      exact preservesLimit_of_isIso_post _ _ }
  exact Limits.preservesLimitsOfShape_of_natIso M.toSchemeIso

/-- The comparison with schemes preserves countable colimits when they exist. -/
theorem preservesColimitsOfShape {C : Cat.{u, v}} {F : C ⥤ Scheme.{u}}
    (M : SchAlphaPresentation C F) (hM : M.IsValid)
    (J : Type) [SmallCategory J] [CountableCategory J] :
    Limits.PreservesColimitsOfShape J F := by
  letI : Limits.PreservesColimitsOfShape J (vonNeumannStage M.ordinal).ι := {
    preservesColimit := fun {K} ↦ Limits.PreservesColimit.mk' fun hK ↦ by
      letI := hK
      haveI := (hM.2.hasColimit_iff K).mp hK
      haveI := hM.2.isIso_colimit_post K
      exact preservesColimit_of_isIso_post _ _ }
  exact Limits.preservesColimitsOfShape_of_natIso M.toSchemeIso

/-- An anchored carrier represents the terminal scheme. In particular it
cannot be empty, even when no seed schemes were selected. -/
theorem exists_iso_specZ {C : Cat.{u, v}} {F : C ⥤ Scheme.{u}}
    (M : SchAlphaPresentation C F) (hM : M.IsValid) :
    ∃ X : C, Nonempty (F.obj X ≅ Spec (CommRingCat.of (ULift.{u} ℤ))) := by
  haveI : Limits.HasTerminal C :=
    ⟨fun K ↦ (M.hasLimit_iff hM K).mpr inferInstance⟩
  letI := M.preservesLimitsOfShape hM (Discrete PEmpty)
  exact ⟨Limits.terminal C,
    ⟨(Limits.IsTerminal.isTerminalObj F _ Limits.terminalIsTerminal).uniqueUpToIso
      specULiftZIsTerminal⟩⟩

/-- Empty carriers cannot carry a valid `Sch_α` comparison. -/
theorem nonempty {C : Cat.{u, v}} {F : C ⥤ Scheme.{u}}
    (M : SchAlphaPresentation C F) (hM : M.IsValid) : Nonempty C := by
  let K := Functor.empty.{0} (vonNeumannStage M.ordinal).FullSubcategory
  haveI : Limits.HasColimit K := (hM.2.hasColimit_iff K).mpr inferInstance
  exact ⟨M.equivalence.inverse.obj (Limits.colimit K)⟩

end SchAlphaPresentation

end Scheme

/-- A chosen big site whose underlying schemes are explicitly identified with
a category `Sch_α` constructed as in Stacks, Tag 000J. Seed objects are already
objects of this category, so the required inclusion of the seeds is automatic.
The local presentation interface remains available as `toChosenBigSite`. -/
structure SchAlphaBigSite (P : Precoverage Scheme.{u}) extends ChosenBigSite.{u, v} P where
  /-- The actual comparison with `Sch_α`, including its scheme functor. -/
  presentation : Scheme.SchAlphaPresentation carrier toScheme
  /-- The comparison level satisfies the construction conditions of Tag 000J. -/
  valid : presentation.IsValid

namespace SchAlphaBigSite

/-- Pullbacks in the native `Sch_α` category follow from its countable-limit
closure, rather than an extra choice of scheme objects. -/
theorem stageHasPullbacks (α : Ordinal.{u})
    (hα : Scheme.IsSmallBoundClosed (Scheme.vonNeumannStage α)) :
    Limits.HasPullbacks (Scheme.vonNeumannStage α).FullSubcategory where
  has_limit K := (hα.hasLimit_iff K).mpr inferInstance

/-- Small fppf covering families on the actual `Sch_α` category. No
representative of an arbitrary ambient cover source is chosen. -/
def stageFppfCovering (α : Ordinal.{u})
    {X : (Scheme.vonNeumannStage α).FullSubcategory} (R : Presieve X) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X.obj,
    R.map (Scheme.vonNeumannStage α).ι = Presieve.ofArrows 𝒰.X 𝒰.f

/-- Smallness of the carrier makes its fppf covering families exactly the
families whose images cover in schemes. -/
theorem stageFppfCovering_iff (α : Ordinal.{u})
    (hsmall : ObjectProperty.Small.{u} (Scheme.vonNeumannStage α))
    {X : (Scheme.vonNeumannStage α).FullSubcategory} (R : Presieve X) :
    stageFppfCovering α R ↔
      R.map (Scheme.vonNeumannStage α).ι ∈ Scheme.fppfPrecoverage X.obj := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    rw [h𝒰]
    exact 𝒰.mem₀
  · intro hR
    letI := hsmall
    let e := (equivShrink.{u} R.uncurry).symm
    have hR' : R = Presieve.ofArrows (fun i : R.uncurry ↦ i.1.1)
        (fun i ↦ i.1.2) := by
      apply le_antisymm
      · intro Y f hf
        exact .mk (⟨⟨Y, f⟩, hf⟩ : R.uncurry)
      · rintro Y f ⟨i⟩
        exact i.2
    have heq : R = Presieve.ofArrows (fun i ↦ (e i).1.1) (fun i ↦ (e i).1.2) :=
      hR'.trans (Presieve.ofArrows_comp_eq_of_surjective _ e.surjective).symm
    refine ⟨{
      I₀ := Shrink.{u} R.uncurry
      X := fun i ↦ (e i).1.1.obj
      f := fun i ↦ (Scheme.vonNeumannStage α).ι.map (e i).1.2
      mem₀ := ?_ }, ?_⟩
    · change Presieve.ofArrows _ _ ∈ Scheme.fppfPrecoverage X.obj
      simpa only [heq, Presieve.map_ofArrows, ObjectProperty.ι_obj] using hR
    · exact (congrArg (Presieve.map (Scheme.vonNeumannStage α).ι) heq).trans
        (Presieve.map_ofArrows _)

/-- The fppf pretopology with its actual small covering families on `Sch_α`.
Only the site laws are proof obligations; the covering predicate is explicit. -/
def stageFppfPretopology (α : Ordinal.{u})
    (hα : Scheme.IsSmallBoundClosed (Scheme.vonNeumannStage α)) :
    @Pretopology (Scheme.vonNeumannStage α).FullSubcategory _
      (stageHasPullbacks α hα) := by
  letI := stageHasPullbacks α hα
  letI : Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (Scheme.vonNeumannStage α).ι := {
    preservesLimit := fun {K} ↦ Limits.PreservesLimit.mk' fun hK ↦ by
      letI := hK
      haveI := (hα.hasLimit_iff K).mp hK
      haveI := hα.isIso_limit_post K
      exact preservesLimit_of_isIso_post _ _ }
  letI : Scheme.fppfPrecoverage.HasIsos := by
    constructor
    intro X Y f hf
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _
      (Precoverage.mem_coverings_of_isIso (J := Scheme.zariskiPrecoverage) f)
  let J := (Scheme.fppfPrecoverage.comap (Scheme.vonNeumannStage α).ι).toPretopology
  exact {
    coverings := fun _ ↦ {R | stageFppfCovering α R}
    has_isos := fun {_ _} f _ ↦ (stageFppfCovering_iff α hα.small _).mpr (J.has_isos f)
    pullbacks := fun {_ _} f R hR ↦ (stageFppfCovering_iff α hα.small _).mpr
      (J.pullbacks f R ((stageFppfCovering_iff α hα.small R).mp hR))
    transitive := fun {_} R Ti hR hTi ↦ (stageFppfCovering_iff α hα.small _).mpr
      (J.transitive R Ti ((stageFppfCovering_iff α hα.small R).mp hR)
        (fun {_} f hf ↦ (stageFppfCovering_iff α hα.small _).mp (hTi f hf))) }

/-- The bounded category `Sch_α` with its fppf families satisfies the local
site laws. General ambient fppf covers admit refinements; their original
sources need not belong to `Sch_α` (Stacks, Tag 03WX). -/
theorem stageFppf_specification (α : Ordinal.{u})
    (hα : Scheme.IsSmallBoundClosed (Scheme.vonNeumannStage α)) :
    IsChosenBigSite Scheme.fppfPrecoverage
      (Cat.of (Scheme.vonNeumannStage α).FullSubcategory)
      (stageHasPullbacks α hα) (Scheme.vonNeumannStage α).ι
      ∅ (fun _ ↦ ∅) (stageFppfPretopology α hα) := by
  sorry

/-- The actual bounded fppf model at any level supplied by Tag 000J. The level
is explicit input: no ordinal, object, functor, or comparison is selected from
an admitted existence theorem. Empty seed sets are allowed by Tag 021R. -/
def fppf (α : Ordinal.{u})
    (hα : Order.IsSuccLimit α ∧
      Scheme.IsSmallBoundClosed (Scheme.vonNeumannStage α)) :
    SchAlphaBigSite.{u, u + 1} Scheme.fppfPrecoverage where
  carrier := Cat.of (Scheme.vonNeumannStage α).FullSubcategory
  hasPullbacks := stageHasPullbacks α hα.2
  toScheme := (Scheme.vonNeumannStage α).ι
  fullyFaithful := (Scheme.vonNeumannStage α).fullyFaithfulι
  seedSchemes := ∅
  seedCoverings := fun _ ↦ ∅
  pretopology := stageFppfPretopology α hα.2
  specification := stageFppf_specification α hα.2
  presentation := {
    ordinal := α
    equivalence := CategoryTheory.Equivalence.refl
    toSchemeIso := Functor.leftUnitor _ }
  valid := hα

/-- The bounded model has exactly the native `Sch_α` carrier. -/
@[simp]
theorem fppf_carrier (α : Ordinal.{u})
    (hα : Order.IsSuccLimit α ∧
      Scheme.IsSmallBoundClosed (Scheme.vonNeumannStage α)) :
    (fppf α hα).carrier = Cat.of (Scheme.vonNeumannStage α).FullSubcategory := rfl

/-- The bounded model's scheme functor is the actual full-subcategory inclusion. -/
@[simp]
theorem fppf_toScheme (α : Ordinal.{u})
    (hα : Order.IsSuccLimit α ∧
      Scheme.IsSmallBoundClosed (Scheme.vonNeumannStage α)) :
    (fppf α hα).toScheme = (Scheme.vonNeumannStage α).ι := rfl

/-- Although the native full subcategory lives in the ambient object universe,
its object type is `u`-small, as required of the bounded model. -/
theorem fppf_small (α : Ordinal.{u})
    (hα : Order.IsSuccLimit α ∧
      Scheme.IsSmallBoundClosed (Scheme.vonNeumannStage α)) :
    Small.{u} (fppf α hα).carrier := by
  letI := hα.2.small
  exact inferInstanceAs (Small.{u} (Scheme.vonNeumannStage α).FullSubcategory)

end SchAlphaBigSite

end AlgebraicGeometry
