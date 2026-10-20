/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart.GlobalEtaComparison
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.Constructed
public import ReasLib.AlgebraicGeometry.LocalizedChern.DerivedEnvelopeCaps
public import ReasLib.AlgebraicGeometry.LocalizedChern.Situation
public import ReasLib.AlgebraicGeometry.BivariantClass.GysinAtInfinity

/-!
# Graph deformation and the localized infinity class

The graph deformation of a perfect derived module carries a characteristic
class on the inverse image of the closed center. Envelope descent constructs
this characteristic class, and descent along the closed cover of the infinity
fiber gives its localized infinity class.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.PerfectGraphAtlas
noncomputable section
universe u

namespace AlgebraicGeometry.LocalizedChern.GlobalProducer

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
  (X : Over S) [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
  (i : Z ⟶ X.left) [IsClosedImmersion i]
  (classes : ChernClass.Theory δ X.hom)
  (E : RingedSpace.ModuleDerived X.left.toRingedSpace) (q : ℕ)
  (mode : RestrictionBehavior) (situation : Situation S δ X i E q mode)

/-- The projection from the relative projective-line family to its base scheme. -/
abbrev projection : ProjectiveLineFamily.space X ⟶ X.left :=
  pullback.fst X.hom (ProjectiveSpace.toBase 1 S)

/-- The infinity divisor of the relative projective-line family. -/
abbrev divisor := BivariantClass.GysinAtInfinity.ambientInfinityDivisor X

/-- The graph deformation scheme of the perfect derived module along infinity. -/
def W : Scheme.{u} := globalW E situation.perfect (projection X) (divisor X)

/-- The structural morphism from the graph deformation to the projective-line family. -/
def b : W δ X i E q mode situation ⟶ ProjectiveLineFamily.space X :=
  globalB E situation.perfect (projection X) (divisor X)

/-- The derived module on the graph deformation obtained by gluing the Rees complexes. -/
def Q : RingedSpace.ModuleDerived (W δ X i E q mode situation).toRingedSpace :=
  globalQ E situation.perfect (projection X) (divisor X)

/-- The closed subscheme of the infinity fiber obtained from the Rees graph construction. -/
def T : Scheme.{u} := globalT E situation.perfect (projection X) (divisor X)

/-- The pullback of the infinity divisor to the graph deformation. -/
abbrev graphDivisor := globalDivisor E situation.perfect (projection X) (divisor X)

/-- The structural morphism of the graph deformation is proper. -/
instance b_proper : IsProper (b δ X i E q mode situation) := by
  sorry

/-- The graph deformation is an isomorphism over the affine complement of infinity. -/
theorem b_affine_iso : IsIso
    (b δ X i E q mode situation ∣_ BivariantClass.GysinAtInfinity.affinePart X) := by
  sorry

/-- The inclusion from the pullback infinity divisor into its zero-scheme presentation. -/
def toInfinity : (graphDivisor δ X i E q mode situation).subscheme ⟶
    (BivariantClass.GysinAtInfinity.infinityFiber X (b δ X i E q mode situation)).left :=
  Scheme.IdealSheafData.inclusion
    (BivariantClass.GysinAtInfinity.infinityDivisor_eq_comap X
      (b δ X i E q mode situation)).le

/-- The canonical inclusion of the Rees graph's closed subscheme into the infinity fiber. -/
def t : T δ X i E q mode situation ⟶
    (BivariantClass.GysinAtInfinity.infinityFiber X (b δ X i E q mode situation)).left :=
  globalTToDivisor E situation.perfect (projection X) (divisor X) ≫
    toInfinity δ X i E q mode situation

/-- The canonical map from the Rees graph's closed subscheme is a closed immersion. -/
instance t_closed : IsClosedImmersion (t δ X i E q mode situation) := by
  sorry

/-- The locus in the Rees graph's closed subscheme where the derived module vanishes,
or is concentrated in degree zero with finite locally free rank less than `q`. -/
def Tprime : Scheme.{u} :=
  if mode.isRankBound then globalTRankLT E situation.perfect (projection X) (divisor X) q
  else globalTVanishing E situation.perfect (projection X) (divisor X)

/-- The inclusion of the vanishing or rank-bound locus in the Rees graph's closed subscheme. -/
def tprime : Tprime δ X i E q mode situation ⟶ T δ X i E q mode situation := by
  unfold Tprime
  split
  · exact globalTRankLTInclusion E situation.perfect (projection X) (divisor X) q
  · exact globalTVanishingInclusion E situation.perfect (projection X) (divisor X)

/-- The vanishing or rank-bound locus is open in the Rees graph's closed subscheme. -/
instance tprime_open : IsOpenImmersion (tprime δ X i E q mode situation) := by
  sorry

/-- The vanishing or rank-bound locus is closed in the Rees graph's closed subscheme. -/
instance tprime_closed : IsClosedImmersion (tprime δ X i E q mode situation) := by
  sorry

/-- The infinity fiber of the graph deformation, regarded as a scheme over `S`. -/
abbrev infinity : Over S :=
  BivariantClass.GysinAtInfinity.infinityFiber X (b δ X i E q mode situation)

/-- The structural morphism from the infinity fiber to the original scheme. -/
abbrev infinityToX : infinity δ X i E q mode situation ⟶ X :=
  BivariantClass.GysinAtInfinity.infinityToX X (b δ X i E q mode situation)

/-- The inverse image of the closed center in the infinity fiber. -/
abbrev center : Over S :=
  pullback (infinityToX δ X i E q mode situation) (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)

/-- The inclusion of the inverse-image center into the infinity fiber. -/
abbrev centerMap : center δ X i E q mode situation ⟶ infinity δ X i E q mode situation :=
  pullback.fst _ _

/-- The infinity fiber is locally of finite type over `S`. -/
instance infinity_finiteType : LocallyOfFiniteType (infinity δ X i E q mode situation).hom := by
  infer_instance

/-- The inverse-image center is locally of finite type over `S`. -/
instance center_finiteType : LocallyOfFiniteType (center δ X i E q mode situation).hom := by
  sorry

/-- The inclusion of the inverse-image center in the infinity fiber is a closed immersion. -/
instance center_closed : IsClosedImmersion (centerMap δ X i E q mode situation).left := by
  sorry

/-- The derived pullback of the graph complex to the inverse-image center. -/
def centerInput : RingedSpace.ModuleDerived (center δ X i E q mode situation).left.toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    ((centerMap δ X i E q mode situation).left ≫
      (BivariantClass.GysinAtInfinity.infinityInclusion X (b δ X i E q mode situation)).left).toShHom).obj
    (Q δ X i E q mode situation)

/-- The restriction of the graph complex to the inverse-image center is perfect. -/
theorem centerInput_perfect : RingedSpace.ModuleDerived.IsPerfect (centerInput δ X i E q mode situation) := by
  sorry

/-- The restricted graph complex admits an envelope on which its derived pullback
has a locally bounded finite locally free representative. -/
theorem centerInput_defined :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ (center δ X i E q mode situation).left), IsEnvelope f ∧
      RingedSpace.ModuleDerived.HasLocallyBoundedFiniteLocallyFreeRepresentative
        ((RingedSpace.modulePullbackDerived f.toShHom).obj (centerInput δ X i E q mode situation)) := by
  sorry

/-- The degree-`q` Newton or Chern class of the graph complex on the inverse-image center,
constructed by envelope descent. -/
def ambient : BivariantClass δ (𝟙 (center δ X i E q mode situation)) (q : ℤ) :=
  EnvelopeCaps.derivedClass δ (classes.reanchor (center δ X i E q mode situation))
    (centerInput δ X i E q mode situation) (centerInput_perfect δ X i E q mode situation)
    (centerInput_defined δ X i E q mode situation) mode.isRankBound q

/-- The inclusion of the vanishing or rank-bound locus into the infinity fiber. -/
abbrev firstMap := tprime δ X i E q mode situation ≫ t δ X i E q mode situation

/-- The vanishing or rank-bound locus is a closed subscheme of the infinity fiber. -/
instance firstMap_closed : IsClosedImmersion (firstMap δ X i E q mode situation) := by
  infer_instance

/-- The vanishing or rank-bound locus and the inverse-image center cover the infinity fiber. -/
theorem cover : Set.range (firstMap δ X i E q mode situation) ∪
    Set.range (centerMap δ X i E q mode situation).left = Set.univ := by
  sorry

/-- The identity on the inverse-image center identifies its structure morphism with
the composite through the infinity fiber. -/
def centerDisplayIso : center δ X i E q mode situation ≅
    Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom) :=
  Over.isoMk (Iso.refl _) (by
    exact (Category.id_comp _).trans (centerMap δ X i E q mode situation).w)

/-- The characteristic class on the inverse-image center, transported to its structure
morphism through the infinity fiber. -/
def ambientDisplay : BivariantClass δ
    (𝟙 (Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom)))
    (q : ℤ) :=
  BivariantClass.restrict δ (centerDisplayIso δ X i E q mode situation).inv
    (𝟙 _) (centerDisplayIso δ X i E q mode situation).inv IsPullback.of_id_snd (q : ℤ)
    (ambient δ X i classes E q mode situation)

/-- The characteristic class vanishes on the intersection of the inverse-image center
with the vanishing or rank-bound locus. -/
theorem intersection_vanishing : Constructed.IntersectionVanishes δ
    (firstMap δ X i E q mode situation) (centerMap δ X i E q mode situation).left
    (q : ℤ) (ambientDisplay δ X i classes E q mode situation) := by
  sorry

/-- The localized infinity class on the inverse-image center with structure morphism
factored through the infinity fiber. -/
def infinityLocalizedDisplay : BivariantClass δ
    (Over.homMk (centerMap δ X i E q mode situation).left :
      Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom) ⟶
        infinity δ X i E q mode situation) (q : ℤ) :=
  Constructed.localized δ (firstMap δ X i E q mode situation)
    (centerMap δ X i E q mode situation).left (q : ℤ)
    (ambientDisplay δ X i classes E q mode situation) (cover δ X i E q mode situation)
    (intersection_vanishing δ X i classes E q mode situation)

/-- The identity identification of the inverse-image center gives a cartesian square
over the infinity fiber. -/
theorem centerPresentationSquare : IsPullback (centerDisplayIso δ X i E q mode situation).hom.left
    (centerMap δ X i E q mode situation).left
    (Over.homMk (centerMap δ X i E q mode situation).left :
      Over.mk ((centerMap δ X i E q mode situation).left ≫ (infinity δ X i E q mode situation).hom) ⟶
        infinity δ X i E q mode situation).left
      ((𝟙 (infinity δ X i E q mode situation) :
        infinity δ X i E q mode situation ⟶ infinity δ X i E q mode situation)).left := by
  sorry

/-- The localized infinity class supported on the inverse-image center. -/
def localizedInfinity : BivariantClass δ (centerMap δ X i E q mode situation) (q : ℤ) :=
  BivariantClass.restrict δ (centerDisplayIso δ X i E q mode situation).hom
    (centerMap δ X i E q mode situation) (𝟙 (infinity δ X i E q mode situation))
    (centerPresentationSquare δ X i E q mode situation) (q : ℤ)
    (infinityLocalizedDisplay δ X i classes E q mode situation)

end AlgebraicGeometry.LocalizedChern.GlobalProducer
