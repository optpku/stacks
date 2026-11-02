/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective.Characterization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.BaseLocus

/-!
# Unramified-and-universally-injective base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which the base
change of `f` is simultaneously unramified and universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UnramifiedUniversallyInjective

/-- The morphism `p₂ : X ×_Y X ⟶ Z` obtained by composing a projection of
the self-fibre product with `f ≫ q`. -/
def selfFiberToBase {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : pullback f f ⟶ Z :=
  pullback.fst f f ≫ f ≫ q

/-- `selfFiberToBase f q` is `pullback.fst f f ≫ f ≫ q`. -/
theorem selfFiberToBase_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) :
    selfFiberToBase f q = pullback.fst f f ≫ f ≫ q :=
  rfl

/-- The two projections of `X ×_Y X` compose equally with `f ≫ q`. -/
theorem selfFiberToBase_fst_eq_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) :
    pullback.fst f f ≫ f ≫ q = pullback.snd f f ≫ f ≫ q :=
  pullback.condition_assoc q

/-- The set of points of `Z` whose `selfFiberToBase`-fibre lies in the image of
the relative diagonal, as the complement of the image under `selfFiberToBase`
of the complement of the image of `pullback.diagonal f`. -/
def diagonalFiberLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map (selfFiberToBase f q) ''
      (Set.range (Points.map (pullback.diagonal f)))ᶜ)ᶜ

/-- The set of points of `Z` over which `f` is unramified on the fibre in `X`
and the fibre of `selfFiberToBase` lies in the image of the relative
diagonal. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  Unramified.baseLocusPointsSet f q ∩ diagonalFiberLocusPointsSet f q

/-- The combined point-set condition, without the hypotheses needed to construct
its open subspace. -/
theorem mem_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (z : Points Z) :
    z ∈ baseLocusPointsSet f q ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x) ∧
        ∀ t : Points (pullback f f),
          Points.map (selfFiberToBase f q) t = z →
            t ∈ Set.range (Points.map (pullback.diagonal f)) :=
  by
    classical
    simp only [baseLocusPointsSet, Unramified.baseLocusPointsSet,
      Unramified.sourceLocus_pointsSet_eq, diagonalFiberLocusPointsSet,
      Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hu, hd⟩
      constructor
      · intro x hx
        by_contra h
        exact hu ⟨x, h, hx⟩
      · intro t ht
        by_contra h
        exact hd ⟨t, h, ht⟩
    · rintro ⟨hu, hd⟩
      constructor
      · rintro ⟨x, hx, h⟩
        exact hx (hu x h)
      · rintro ⟨t, ht, h⟩
        exact ht (hd t h)

/-- The unramified-and-universally-injective base locus of the triangle is open
in `Points Z` when `f ≫ q` is locally of finite type and closed and
`selfFiberToBase f q` is closed. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    IsOpen (baseLocusPointsSet f q) := by
  classical
  let U := Unramified.sourceLocus f
  let i := U.ι
  letI : IsOpenImmersion i := U.isOpenImmersion
  let m := pullback.map (i ≫ f) (i ≫ f) f f i i (𝟙 Y) (by simp) (by simp)
  have hm : IsOpenImmersion m :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion S)
      (show IsOpenImmersion i from inferInstance)
      (show IsOpenImmersion i from inferInstance) rfl rfl
  have heq : pullback.diagonal (i ≫ f) ≫ m = i ≫ pullback.diagonal f := by
    ext <;> simp [m, pullback.map, pullback.lift_fst, pullback.lift_snd]
  haveI : Unramified (i ≫ f) := Unramified.sourceLocus_unramified f
  haveI : IsOpenImmersion m := hm
  haveI : IsOpenImmersion (i ≫ pullback.diagonal f) := by
    rw [← heq]
    infer_instance
  have hopen : IsOpen (Set.range (Points.map (i ≫ pullback.diagonal f))) :=
    OpenSubspace.isOpen_pointsSet (OpenSubspace.ofι (i ≫ pullback.diagonal f))
  have hfst (x : Points X) :
      Points.map (pullback.fst f f) (Points.map (pullback.diagonal f) x) = x := by
    rw [← Points.map_comp, pullback.diagonal_fst, Points.map_id]
  have hbase (x : Points X) :
      Points.map (selfFiberToBase f q) (Points.map (pullback.diagonal f) x) =
        Points.map (f ≫ q) x := by
    rw [← Points.map_comp]
    simp only [selfFiberToBase, pullback.diagonal_fst_assoc]
  have hset : baseLocusPointsSet f q =
      (Points.map (selfFiberToBase f q) ''
        (Set.range (Points.map (i ≫ pullback.diagonal f)))ᶜ)ᶜ := by
    ext z
    rw [mem_baseLocusPointsSet]
    change _ ↔ ¬ ∃ t, t ∉ Set.range (Points.map (i ≫ pullback.diagonal f)) ∧
      Points.map (selfFiberToBase f q) t = z
    constructor
    · rintro ⟨hu, hd⟩ ⟨t, ht, hz⟩
      obtain ⟨x, rfl⟩ := hd t hz
      have hx : UnramifiedAt f x := hu x ((hbase x).symm.trans hz)
      obtain ⟨a, ha⟩ := (Unramified.mem_sourceLocus f x).mpr hx
      apply ht
      exact ⟨a, by rw [Points.map_comp]; exact congrArg (Points.map (pullback.diagonal f)) ha⟩
    · intro h
      constructor
      · intro x hx
        have hxdiag : Points.map (pullback.diagonal f) x ∈
            Set.range (Points.map (i ≫ pullback.diagonal f)) := by
          by_contra hn
          exact h ⟨_, hn, (hbase x).trans hx⟩
        obtain ⟨a, ha⟩ := hxdiag
        rw [Points.map_comp] at ha
        have hax := congrArg (Points.map (pullback.fst f f)) ha
        rw [hfst, hfst] at hax
        exact (Unramified.mem_sourceLocus f x).mp ⟨a, hax⟩
      · intro t ht
        have hmem : t ∈ Set.range (Points.map (i ≫ pullback.diagonal f)) := by
          by_contra hn
          exact h ⟨t, hn, ht⟩
        obtain ⟨a, rfl⟩ := hmem
        exact ⟨Points.map i a, (Points.map_comp i (pullback.diagonal f) a).symm⟩
  rw [hset]
  exact (Closed.isClosedMap (f := selfFiberToBase f q) _ hopen.isClosed_compl).isOpen_compl

/-- The unramified-and-universally-injective base locus of the triangle, as an
open of `Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] : Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is unramified and universally injective after base change to the point. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    OpenSubspace Z :=
  OpenSubspace.fromOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  OpenSubspace.fromOpens_pointsSet (baseLocusPoints f q)

/-- A point of `Z` lies in the unramified-and-universally-injective base locus
if and only if `f` is unramified at every point of `X` above it and the fibre
of `selfFiberToBase` over it lies in the image of the relative diagonal. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x) ∧
        ∀ t : Points (pullback f f),
          Points.map (selfFiberToBase f q) t = z →
            t ∈ Set.range (Points.map (pullback.diagonal f)) := by
  rw [baseLocus_pointsSet_eq]
  exact mem_baseLocusPointsSet f q z

/-- A map to the base lands in the diagonal-fibre locus exactly when the
induced base change is universally injective. -/
theorem range_subset_diagonalFiberLocusPointsSet_iff {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    Set.range (Points.map g) ⊆ diagonalFiberLocusPointsSet f q ↔
      UniversallyInjective (Unramified.overBaseChange f q g) := by
  classical
  let F := Unramified.overBaseChange f q g
  let a := pullback.fst (f ≫ q) g
  let b := pullback.fst q g
  let c := pullback.snd (f ≫ q) g
  have hfst : F ≫ b = a ≫ f := by
    simp [F, b, a, Unramified.overBaseChange, pullback.map, pullback.lift_fst]
  have hsnd : F ≫ pullback.snd q g = c := by
    simp [F, c, Unramified.overBaseChange, pullback.map, pullback.lift_snd]
  have hX := IsPullback.of_hasPullback (f ≫ q) g
  have hY := IsPullback.of_hasPullback q g
  have hF : IsPullback a F f b := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd q g) (v₂₂ := q) ?_
      hfst.symm hY
    simpa only [hsnd] using hX
  let d := pullback.map F F f f a a b
    hfst hfst
  have houter : IsPullback (d ≫ pullback.fst f f) (pullback.snd F F) f (a ≫ f) := by
    simpa only [d, pullback.map, pullback.lift_fst, hfst] using
      (IsPullback.of_hasPullback F F).paste_horiz hF
  have hself : IsPullback d (pullback.snd F F) (pullback.snd f f) a :=
    houter.of_right (by simp only [d, pullback.map, pullback.lift_snd])
      (IsPullback.of_hasPullback f f)
  have hT : IsPullback d (pullback.snd F F ≫ c) (selfFiberToBase f q) g := by
    simpa only [selfFiberToBase, Category.assoc, ← selfFiberToBase_fst_eq_snd] using
      hself.paste_vert hX
  have hδ : IsPullback a (pullback.diagonal F) (pullback.diagonal f) d := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd F F ≫ c)
      (v₂₂ := selfFiberToBase f q) ?_ ?_ hT
    · simpa only [Category.assoc, pullback.diagonal_snd_assoc,
        selfFiberToBase, pullback.diagonal_fst_assoc] using hX
    · ext <;> simp [d, pullback.map, pullback.lift_fst, pullback.lift_snd]
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  constructor
  · intro h t
    have ht : Points.map d t ∈ Set.range (Points.map (pullback.diagonal f)) := by
      by_contra hn
      exact h ⟨Points.map (pullback.snd F F ≫ c) t, rfl⟩
        ⟨Points.map d t, hn, Points.pullbackComparison_condition hT t⟩
    obtain ⟨x, hx⟩ := ht
    obtain ⟨x', _, hx'⟩ := Points.exists_of_map_eq hδ x t hx
    exact ⟨x', hx'⟩
  · rintro h _ ⟨z, rfl⟩ ⟨t, ht, hz⟩
    obtain ⟨t', hdt, _⟩ := Points.exists_of_map_eq hT t z hz
    obtain ⟨x', hx'⟩ := h t'
    apply ht
    refine ⟨Points.map a x', ?_⟩
    exact (Points.pullbackComparison_condition hδ x').trans
      ((congrArg (Points.map d) hx').trans hdt)


/-- For a triangle whose composite is locally of finite type and closed, and whose
relative self-fibre product is closed over the base, a morphism to the base factors
through the combined base locus if and only if the induced base change is
unramified and universally injective. -/
@[stacks 05X9]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Unramified (Unramified.overBaseChange f q g) ∧
        UniversallyInjective (Unramified.overBaseChange f q g) :=
  by
    have hu := Unramified.exists_lift_iff_overBaseChange f q g
    rw [(Unramified.baseLocus f q).exists_lift_iff_range_subset g,
      Unramified.baseLocus_pointsSet_eq] at hu
    rw [(baseLocus f q).exists_lift_iff_range_subset g, baseLocus_pointsSet_eq,
      baseLocusPointsSet, Set.subset_inter_iff, hu,
      range_subset_diagonalFiberLocusPointsSet_iff]

/-- The base change of `f` along the inclusion of the
unramified-and-universally-injective base locus is unramified. -/
def baseLocus_unramified {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    Unramified (Unramified.overBaseChange f q (baseLocus f q).ι) :=
  ((exists_lift_iff_overBaseChange f q (baseLocus f q).ι).mp
    ⟨𝟙 _, Category.id_comp _⟩).1

/-- The base change of `f` along the inclusion of the
unramified-and-universally-injective base locus is universally injective. -/
def baseLocus_universallyInjective {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    UniversallyInjective (Unramified.overBaseChange f q (baseLocus f q).ι) :=
  ((exists_lift_iff_overBaseChange f q (baseLocus f q).ι).mp
    ⟨𝟙 _, Category.id_comp _⟩).2

end UnramifiedUniversallyInjective

end AlgebraicGeometry.AlgebraicSpace
