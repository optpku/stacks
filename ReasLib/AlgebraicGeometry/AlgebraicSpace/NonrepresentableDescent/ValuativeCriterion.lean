/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.Space
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent.Descent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.UniversallyClosed

public section

open CategoryTheory Limits Opposite
open scoped PowerSeries LaurentSeries

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent

/-- The doubled-origin line over the original affine-line base. -/
@[expose] def doubledOriginAsOver (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Over (base k) :=
  Over.mk ((doubledOriginOver k k').hom ≫ (cover k k').hom)

/-- The doubled-origin fold as a morphism over the original affine line. -/
@[expose] def doubledOriginToCover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    doubledOriginAsOver k k' ⟶ cover k k' :=
  Over.homMk (doubledOriginOver k k').hom rfl

/-- The underlying morphism of the doubled-origin map is the fold over the cover. -/
theorem doubledOriginToCover_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (doubledOriginToCover k k').left = (doubledOriginOver k k').hom := rfl

/-- The second projection after pulling the quadratic quotient back to its covering line. -/
@[expose] def structureHomPullback (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    pullback (spaceStructureHom k k' hdeg)
      (show ofOver (cover k k') ⟶ ofOver (baseAsOver k) from yoneda.map (coverToBase k k')) ⟶
        ofOver (cover k k') :=
  pullback.snd (spaceStructureHom k k' hdeg)
    (show ofOver (cover k k') ⟶ ofOver (baseAsOver k) from yoneda.map (coverToBase k k'))

/-- The pullback projection of the quadratic quotient is the doubled-origin fold,
up to isomorphism over the covering affine line. -/
theorem structureHomPullback_over_iso (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Nonempty (Over.mk (structureHomPullback k k' hdeg) ≅
      Over.mk (show ofOver (doubledOriginAsOver k k') ⟶ ofOver (cover k k') from
        yoneda.map (doubledOriginToCover k k'))) := by
  sorry

/-- The structure morphism of the quadratic Galois quotient is quasi-compact. -/
instance instQuasiCompact_spaceStructureHom (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    QuasiCompact (spaceStructureHom k k' hdeg) := by
  sorry

/-- The structure morphism of the quadratic Galois quotient is universally closed. -/
instance instUniversallyClosed_spaceStructureHom (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    UniversallyClosed (spaceStructureHom k k' hdeg) := by
  sorry

/-- The spectrum map induced by the inclusion of polynomials into power series. -/
@[expose] def powerSeriesHom (k : Type u) [Field k] :
    Spec (CommRingCat.of (PowerSeries k)) ⟶ base k :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (PowerSeries k)))

/-- The power-series spectrum over the affine line via the polynomial inclusion. -/
@[expose] def powerSeriesOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (powerSeriesHom k)

/-- The structure map of the power-series spectrum is induced by the polynomial inclusion. -/
theorem powerSeriesOver_hom (k : Type u) [Field k] :
    (powerSeriesOver k).hom = powerSeriesHom k := rfl

/-- The map from the power-series spectrum to the base in the category over the affine line. -/
@[expose] def powerSeriesToBase (k : Type u) [Field k] : powerSeriesOver k ⟶ baseAsOver k :=
  toBaseAsOver k (powerSeriesOver k)

/-- The spectrum map induced by the inclusion of power series into Laurent series. -/
@[expose] def verticalHom (k : Type u) [Field k] :
    Spec (CommRingCat.of (LaurentSeries k)) ⟶ Spec (CommRingCat.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))

/-- The Laurent-series spectrum over the affine line through the power-series spectrum. -/
@[expose] def laurentOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (verticalHom k ≫ (powerSeriesOver k).hom)

/-- The structure map of the Laurent-series spectrum factors through the power-series spectrum. -/
theorem laurentOver_hom (k : Type u) [Field k] :
    (laurentOver k).hom = verticalHom k ≫ (powerSeriesOver k).hom := rfl

/-- The inclusion of power series into Laurent series induces a morphism over the affine line. -/
@[expose] def vertical (k : Type u) [Field k] : laurentOver k ⟶ powerSeriesOver k :=
  Over.homMk (verticalHom k) rfl

/-- The underlying arrow of the Laurent-series to power-series map is the spectrum inclusion. -/
theorem vertical_left (k : Type u) [Field k] :
    (vertical k).left = verticalHom k := rfl

/-- The Laurent-series test map lands in the punctured affine line. -/
theorem laurent_range_subset_punctured (k : Type u) [Field k] :
    Set.range (fun x : (laurentOver k).left ↦ (laurentOver k).hom x) ⊆
      basePuncturedOpen k := by
  sorry

private def laurentLocalCover (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) : (laurentOver k).left.Etale :=
  MorphismProperty.Over.mk _ (pullback.snd (cover k k').hom (laurentOver k).hom)
    (MorphismProperty.pullback_snd (cover k k').hom (laurentOver k).hom
      (etale_cover_hom k k' hdeg))

private def laurentLocalSections (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    (Scheme.EtaleSheafification.localSheaf (preRelation k k' hdeg).quotientPresheaf
      (laurentOver k)).obj.obj (op (laurentLocalCover k k' hdeg)) :=
  (CategoryTheory.toSheafify (laurentOver k).left.smallEtaleTopology
    (Scheme.EtaleSheafification.restriction (preRelation k k' hdeg).quotientPresheaf
      (laurentOver k))).app (op (laurentLocalCover k k' hdeg))
    (Quot.mk ((preRelation k k' hdeg).pointRel _)
      (Over.homMk (pullback.fst (cover k k').hom (laurentOver k).hom)
        (pullback.condition.trans (by rfl))))

private theorem laurentLocalSections_compatible (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2)
    {W : (laurentOver k).left.Etale}
    (a b : W ⟶ laurentLocalCover k k' hdeg)
    (h : a ≫ (show laurentLocalCover k k' hdeg ⟶
          Scheme.Etale.mk (𝟙 (laurentOver k).left) from
          MorphismProperty.Over.homMk (laurentLocalCover k k' hdeg).hom
            (Category.comp_id _)) =
      b ≫ (show laurentLocalCover k k' hdeg ⟶
          Scheme.Etale.mk (𝟙 (laurentOver k).left) from
          MorphismProperty.Over.homMk (laurentLocalCover k k' hdeg).hom
            (Category.comp_id _))) :
    (Scheme.EtaleSheafification.localSheaf (preRelation k k' hdeg).quotientPresheaf
      (laurentOver k)).obj.map a.op (laurentLocalSections k k' hdeg) =
    (Scheme.EtaleSheafification.localSheaf (preRelation k k' hdeg).quotientPresheaf
      (laurentOver k)).obj.map b.op (laurentLocalSections k k' hdeg) := by
  sorry

/-- The Laurent-series section of the quadratic quotient, obtained by amalgamating the
explicit quotient classes on the base change of the covering affine line. -/
def laurentSection (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    (space k k' hdeg).functorOfPoints.obj (op (laurentOver k)) := by
  let L := Scheme.EtaleSheafification.localSheaf
    (preRelation k k' hdeg).quotientPresheaf (laurentOver k)
  let q : laurentLocalCover k k' hdeg ⟶ Scheme.Etale.mk (𝟙 (laurentOver k).left) :=
    MorphismProperty.Over.homMk (laurentLocalCover k k' hdeg).hom (Category.comp_id _)
  have hq : Sieve.ofArrows (fun _ : PUnit.{1} ↦ laurentLocalCover k k' hdeg)
      (fun _ ↦ q) ∈ (laurentOver k).left.smallEtaleTopology _ := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    simp only [Set.iUnion_const]
    exact Set.range_eq_univ.mpr
      (MorphismProperty.pullback_snd (cover k k').hom (laurentOver k).hom
        (surjective_cover_hom k k' hdeg)).surj
  exact (Presheaf.IsSheaf.amalgamateOfArrows L.property (fun _ : PUnit.{1} ↦ q) hq
    (fun _ ↦ TypeCat.ofHom fun _ : PUnit.{u + 1} ↦ laurentLocalSections k k' hdeg)
    (by
      intro W i j a b h
      ext x
      exact laurentLocalSections_compatible k k' hdeg a b h)) PUnit.unit

/-- The Laurent-series section lies over the structure map of its test scheme. -/
theorem laurentSection_spec (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    (spaceStructureHom k k' hdeg).app (op (laurentOver k)) (laurentSection k k' hdeg) =
      toBaseAsOver k (laurentOver k) := rfl

/-- The morphism from the Laurent-series spectrum corresponding to its quotient section. -/
@[expose] def laurentToSpace (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    ofOver (laurentOver k) ⟶ space k k' hdeg :=
  yonedaEquiv.symm (laurentSection k k' hdeg)

/-- The Laurent-series arrow composes with the quotient structure map to its base map. -/
theorem laurentToSpace_comp_structureHom (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    laurentToSpace k k' hdeg ≫ spaceStructureHom k k' hdeg =
      (show ofOver (laurentOver k) ⟶ ofOver (baseAsOver k) from
        yoneda.map (toBaseAsOver k (laurentOver k))) := by
  sorry

/-- The commutative square given by the Laurent-series and power-series test spectra. -/
theorem valuativeCommSq (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    CommSq (laurentToSpace k k' hdeg)
      (show ofOver (laurentOver k) ⟶ ofOver (powerSeriesOver k) from yoneda.map (vertical k))
      (spaceStructureHom k k' hdeg)
      (show ofOver (powerSeriesOver k) ⟶ ofOver (baseAsOver k) from
        yoneda.map (powerSeriesToBase k)) := by
  constructor
  rw [laurentToSpace_comp_structureHom]
  change yoneda.map (toBaseAsOver k (laurentOver k)) =
    yoneda.map (vertical k) ≫ yoneda.map (powerSeriesToBase k)
  rw [← yoneda.map_comp]
  congr 1
  apply Over.OverMorphism.ext
  change (toBaseAsOver k (laurentOver k)).left =
    (vertical k).left ≫ (toBaseAsOver k (powerSeriesOver k)).left
  rw [toBaseAsOver_left, toBaseAsOver_left]
  rfl

/-- The origin of the covering affine line as a morphism over the base. -/
@[expose] def originToCover (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    originOver k k' ⟶ cover k k' :=
  Over.homMk (originHom k k') rfl

/-- The underlying arrow of the relative origin map is evaluation at zero on spectra. -/
theorem originToCover_left (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (originToCover k k').left = originHom k k' := rfl

/-- The origin morphism into the quotient is the composite with its canonical atlas. -/
@[expose] def originToSpace (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) : ofOver (originOver k k') ⟶ space k k' hdeg :=
  (show ofOver (originOver k k') ⟶ ofOver (cover k k') from
    yoneda.map (originToCover k k')) ≫
  (show ofOver (cover k k') ⟶ space k k' hdeg from spaceAtlas k k' hdeg)

/-- The origin morphism from the spectrum of the quadratic extension to the quotient is mono. -/
instance mono_originToSpace (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [IsGalois k k'] (hdeg : Module.finrank k k' = 2) :
    Mono (originToSpace k k' hdeg) := by
  sorry

/-- The concrete Laurent-series and power-series square has no lift to the quadratic quotient. -/
theorem not_hasLift (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [IsGalois k k']
    (hdeg : Module.finrank k k' = 2) :
    ¬ (valuativeCommSq k k' hdeg).HasLift := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.NonrepresentableDescent
