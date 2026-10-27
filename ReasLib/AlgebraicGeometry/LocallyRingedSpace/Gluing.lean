/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenImmersion
public import ReasLib.CategoryTheory.GlueData
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Mapping properties of glued locally ringed spaces

Mathlib's `LocallyRingedSpace.GlueData` owns the glued object, its open charts, and their
overlaps. The generic categorical layer owns the outgoing mapping property; this file supplies
canonical chart-preimage descent data and the complementary incoming mapping property for
arbitrary literal source opens. The canonical chart-preimage construction is a normalized
subclass of incoming data, not a claim that every chosen source cover is definitionally that
cover. Chart maps reuse the canonical open-immersion restriction API.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

variable (D : LocallyRingedSpace.GlueData.{u})

/-- The outgoing gluing equivalence inherited from the categorical glue-data owner. -/
@[stacks 01JB "categorical gluing descent equivalence"]
noncomputable abbrev homEquiv (Y : LocallyRingedSpace.{u}) :=
  D.toGlueData.homEquiv Y

/-- Incoming descent data for a morphism to a glued locally ringed space. -/
@[stacks 01JB "incoming descent"]
structure IncomingDescent (Y : LocallyRingedSpace.{u}) where
  /-- The source open mapping to the `i`-th chart. -/
  V : D.J → Opens Y
  /-- The source opens cover the source. -/
  isOpenCover : IsOpenCover V
  /-- The local map to the corresponding chart. -/
  g (i : D.J) : Y.restrict (V i).isOpenEmbedding ⟶ D.U i
  /-- The comparison from a source-chart intersection to the corresponding overlap. -/
  overlap (i j : D.J) :
    pullback (Y.ofRestrict (V i).isOpenEmbedding)
      (Y.ofRestrict (V j).isOpenEmbedding) ⟶ D.V (i, j)
  /-- The source-chart intersection is the inverse image of the overlap in the `i`-th chart. -/
  overlap_isPullback (i j : D.J) :
    IsPullback (overlap i j)
      (pullback.fst (Y.ofRestrict (V i).isOpenEmbedding)
        (Y.ofRestrict (V j).isOpenEmbedding)) (D.f i j) (g i)
  /-- The two local chart maps agree through the overlap transition. -/
  overlap_compat (i j : D.J) :
    CommSq (overlap i j ≫ D.t i j)
      (pullback.snd (Y.ofRestrict (V i).isOpenEmbedding)
        (Y.ofRestrict (V j).isOpenEmbedding)) (D.f j i) (g j)

/-- The inverse image in `Y` of the `i`-th chart of a glued locally ringed space. -/
@[stacks 01JB "inverse image of a gluing chart"]
def chartPreimage {Y : LocallyRingedSpace.{u}} (h : Y ⟶ D.glued) (i : D.J) : Opens Y :=
  (Opens.map h.base).obj (D.ι i).opensRange

/-- The inverse images of the gluing charts cover the source. -/
@[stacks 01JB "gluing-chart preimages cover"]
theorem chartPreimage_isOpenCover {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) :
    IsOpenCover (D.chartPreimage h) := sorry

/-- The composite from an inverse-image chart of `Y` to the glued space has image in the
corresponding target chart. -/
@[stacks 01JB "gluing-chart preimage range"]
theorem chartPreimage_range_subset {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i : D.J) :
    Set.range
        ((Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding ≫ h).base) ⊆
      Set.range (D.ι i).base := by
  rintro _ ⟨x, rfl⟩
  exact x.property

/-- The canonical restriction of a morphism into a glued space to the inverse image of one
target chart. -/
@[stacks 01JB "restriction to a gluing chart"]
noncomputable def chartPreimageMap {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i : D.J) :
    Y.restrict (D.chartPreimage h i).isOpenEmbedding ⟶ D.U i :=
  h.restrictToOpenImmersion (D.chartPreimage h i) (D.ι i)
    (D.chartPreimage_range_subset h i)

/-- The canonical chart restriction followed by its chart inclusion is the original morphism on
the inverse-image open. -/
@[reassoc (attr := simp), stacks 01JB]
theorem chartPreimageMap_ι {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i : D.J) :
    D.chartPreimageMap h i ≫ D.ι i =
      Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding ≫ h := sorry

/-- A morphism into a glued space has a unique restriction to each inverse-image chart. -/
@[stacks 01JB "restriction to a gluing chart"]
theorem existsUnique_chartPreimageMap {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i : D.J) :
    ∃! g : Y.restrict (D.chartPreimage h i).isOpenEmbedding ⟶ D.U i,
      g ≫ D.ι i =
        Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding ≫ h := sorry

/-- The two chart-preimage maps form a cone over the canonical pullback presentation of a target
chart overlap. -/
@[stacks 01JB "gluing-chart preimage cone"]
theorem chartPreimageCone_condition {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J) :
    (pullback.fst (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h i) ≫ D.ι i =
      (pullback.snd (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h j) ≫ D.ι j := sorry

/-- The canonical comparison from the intersection of two chart preimages to the corresponding
target-chart overlap. -/
@[stacks 01JB "inverse image of a gluing overlap"]
noncomputable def chartPreimageOverlap {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J) :
    pullback (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
        (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ⟶ D.V (i, j) :=
  (D.vPullbackConeIsLimit i j).lift
    (PullbackCone.mk
      (pullback.fst (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h i)
      (pullback.snd (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h j)
      (D.chartPreimageCone_condition h i j))

/-- The canonical chart-preimage overlap comparison factors through the first target chart. -/
@[reassoc (attr := simp), stacks 01JB "gluing-overlap first projection"]
theorem chartPreimageOverlap_fst {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J) :
    D.chartPreimageOverlap h i j ≫ D.f i j =
      pullback.fst (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h i := sorry

/-- The canonical chart-preimage overlap comparison has the prescribed second projection. -/
@[reassoc (attr := simp), stacks 01JB "gluing-overlap second projection"]
theorem chartPreimageOverlap_snd {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J) :
    D.chartPreimageOverlap h i j ≫ D.t i j ≫ D.f j i =
      pullback.snd (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h j := sorry

/-- The canonical overlap comparison identifies the intersection of chart preimages with the
inverse image of the target overlap. -/
@[stacks 01JB "gluing-overlap pullback"]
theorem chartPreimageOverlap_isPullback {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J) :
    IsPullback (D.chartPreimageOverlap h i j)
      (pullback.fst (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
        (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding))
      (D.f i j) (D.chartPreimageMap h i) := sorry

/-- The two canonical chart-preimage maps agree through the gluing transition on their
intersection. -/
@[stacks 01JB "gluing-overlap transition"]
theorem chartPreimageOverlap_compat {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J) :
    CommSq (D.chartPreimageOverlap h i j ≫ D.t i j)
      (pullback.snd (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
        (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding))
      (D.f j i) (D.chartPreimageMap h j) := sorry

/-- The canonical chart-preimage overlap comparison is unique from its two projections. -/
@[stacks 01JB "gluing-overlap uniqueness"]
theorem chartPreimageOverlap_unique {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J)
    {k : pullback (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
        (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ⟶ D.V (i, j)}
    (hk_fst : k ≫ D.f i j =
      pullback.fst (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h i)
    (hk_snd : k ≫ D.t i j ≫ D.f j i =
      pullback.snd (Y.ofRestrict (D.chartPreimage h i).isOpenEmbedding)
          (Y.ofRestrict (D.chartPreimage h j).isOpenEmbedding) ≫
        D.chartPreimageMap h j) :
    k = D.chartPreimageOverlap h i j := sorry

/-- The canonical incoming descent datum obtained by restricting a morphism to the inverse images
of all gluing charts. -/
@[stacks 01JB "canonical incoming descent"]
noncomputable def incomingDescent {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) : D.IncomingDescent Y where
  V := D.chartPreimage h
  isOpenCover := D.chartPreimage_isOpenCover h
  g := D.chartPreimageMap h
  overlap := D.chartPreimageOverlap h
  overlap_isPullback := D.chartPreimageOverlap_isPullback h
  overlap_compat := D.chartPreimageOverlap_compat h

/-- The source opens of the canonical incoming descent datum are the chart preimages. -/
@[simp, stacks 01JB]
theorem incomingDescent_V {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i : D.J) :
    (D.incomingDescent h).V i = D.chartPreimage h i := sorry

/-- The local maps of the canonical incoming descent datum are the chart-preimage maps. -/
@[simp, stacks 01JB]
theorem incomingDescent_g {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i : D.J) :
    (D.incomingDescent h).g i = D.chartPreimageMap h i := sorry

/-- The overlap maps of the canonical incoming descent datum are the chart-preimage overlap
comparisons. -/
@[simp, stacks 01JB]
theorem incomingDescent_overlap {Y : LocallyRingedSpace.{u}}
    (h : Y ⟶ D.glued) (i j : D.J) :
    (D.incomingDescent h).overlap i j = D.chartPreimageOverlap h i j := sorry

/-- The canonical incoming construction remembers enough data to recover the global morphism. -/
@[stacks 01JB "injectivity of canonical incoming descent"]
theorem incomingDescent_injective (Y : LocallyRingedSpace.{u}) :
  Function.Injective (fun h : Y ⟶ D.glued ↦ D.incomingDescent h) := sorry

namespace IncomingDescent

variable {D : LocallyRingedSpace.GlueData.{u}} {Y : LocallyRingedSpace.{u}}

/-- The inclusion of one source open of an incoming descent datum. -/
@[stacks 01JB "incoming descent source inclusion"]
abbrev sourceInclusion (S : D.IncomingDescent Y) (i : D.J) :
    Y.restrict (S.V i).isOpenEmbedding ⟶ Y :=
  Y.ofRestrict (S.V i).isOpenEmbedding

/-- The first pullback projection of an incoming descent datum factors through its local chart
map. -/
@[reassoc (attr := simp), stacks 01JB "incoming descent first projection"]
theorem overlap_fst (S : D.IncomingDescent Y) (i j : D.J) :
    S.overlap i j ≫ D.f i j =
      pullback.fst (S.sourceInclusion i) (S.sourceInclusion j) ≫ S.g i := sorry

/-- An incoming descent overlap has the prescribed second projection. -/
@[reassoc (attr := simp), stacks 01JB "incoming descent second projection"]
theorem overlap_snd (S : D.IncomingDescent Y) (i j : D.J) :
    S.overlap i j ≫ D.t i j ≫ D.f j i =
      pullback.snd (S.sourceInclusion i) (S.sourceInclusion j) ≫ S.g j := sorry

/-- A global morphism is induced by incoming descent data when its restriction to every source
open is the prescribed local chart map followed by the target chart inclusion. -/
@[stacks 01JB "incoming descent induced morphism"]
def IsInducedBy (S : D.IncomingDescent Y) (h : Y ⟶ D.glued) : Prop :=
  ∀ i, S.sourceInclusion i ≫ h = S.g i ≫ D.ι i

/-- A morphism induces its canonical chart-preimage descent datum. -/
@[stacks 01JB]
theorem canonical_isInducedBy (h : Y ⟶ D.glued) :
    (D.incomingDescent h).IsInducedBy h := sorry

/-- Incoming descent data induce a morphism to the glued locally ringed space. -/
@[stacks 01JB "incoming descent existence"]
theorem exists_hom (S : D.IncomingDescent Y) :
    ∃ h : Y ⟶ D.glued, S.IsInducedBy h := sorry

/-- Two morphisms to the glued space are equal when they agree on every source open of an
incoming descent datum. -/
@[ext, stacks 01JB "incoming descent extensionality"]
theorem hom_ext (S : D.IncomingDescent Y) {f g : Y ⟶ D.glued}
    (h : ∀ i, S.sourceInclusion i ≫ f = S.sourceInclusion i ≫ g) :
    f = g := sorry

/-- A global morphism induced by fixed incoming descent data is unique. -/
@[stacks 01JB]
theorem IsInducedBy.eq (S : D.IncomingDescent Y) {f g : Y ⟶ D.glued}
    (hf : S.IsInducedBy f) (hg : S.IsInducedBy g) :
    f = g := sorry

/-- Compatible incoming descent data induce a unique morphism to the glued locally ringed
space whose restriction to each source open is the prescribed local map. -/
@[stacks 01JB "incoming mapping property"]
theorem existsUnique_hom (S : D.IncomingDescent Y) :
    ∃! h : Y ⟶ D.glued, S.IsInducedBy h := sorry

end IncomingDescent

end AlgebraicGeometry.LocallyRingedSpace.GlueData
