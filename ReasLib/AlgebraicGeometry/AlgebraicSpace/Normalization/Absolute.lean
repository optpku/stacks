/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Over
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientPresheaf.Desc
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Hom
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.CodimensionZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolute normalization of algebraic spaces

Normalize an étale presentation and sheafify its quotient for the fppf topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Limits Opposite

noncomputable section

universe u

open AlgebraicGeometry.Scheme.Normalization AlgebraicGeometry.Scheme.FppfSheafification

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale atlas scheme of `X` whose quasi-compact opens have finitely many irreducible
components, extracted from the class field
`HasFiniteIrreducibleComponentsOnCompactOpens.exists_finiteComponents_etaleCover`. -/
def finiteComponentsScheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] : Over S :=
  Exists.choose hX.exists_finiteComponents_etaleCover

/-- The chosen finite-components étale atlas morphism `ofOver U ⟶ X`. -/
def finiteComponentsAtlas {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    ofOver (finiteComponentsScheme X) ⟶ X :=
  Exists.choose (Exists.choose_spec hX.exists_finiteComponents_etaleCover)

/-- The chosen finite-components atlas is representable and étale as a presheaf morphism. -/
theorem finiteComponentsAtlas_presheaf_etale {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (finiteComponentsAtlas X) :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_etaleCover)).1

/-- The chosen finite-components atlas is étale-locally surjective. -/
theorem finiteComponentsAtlas_locallySurjective {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (finiteComponentsAtlas X) :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_etaleCover)).2.1

/-- The source of the chosen finite-components atlas has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_finiteComponentsScheme
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens (finiteComponentsScheme X).left :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_etaleCover)).2.2

/-- The represented kernel pair `R = U ×_X U` of the chosen finite-components atlas. -/
def finiteComponentsRelation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    PreRelation (finiteComponentsScheme X) :=
  kernelPair (finiteComponentsAtlas X) (finiteComponentsAtlas_presheaf_etale X).rep

/-- The first projection of the chosen finite-components kernel pair is étale. -/
instance instEtale_finiteComponentsRelation_t {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicGeometry.Etale (finiteComponentsRelation X).t.left :=
  sorry

/-- The second projection of the chosen finite-components kernel pair is étale. -/
instance instEtale_finiteComponentsRelation_s {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicGeometry.Etale (finiteComponentsRelation X).s.left :=
  sorry

namespace finiteComponentsRelation

/-- The kernel-pair scheme of a finite-components atlas has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens
      (finiteComponentsRelation X).left.left :=
  Scheme.HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth
    (finiteComponentsRelation X).s.left

end finiteComponentsRelation

/-- The one-sided fibre product `R ×_{s, U} U^ν` of the kernel pair along the étale
projection `s` with `ν_U`. -/
def normalizedRelationPullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] : Over S :=
  pullback (finiteComponentsRelation X).s
    (overNormalizationTo (finiteComponentsScheme X))

/-- The comparison from the normalized kernel pair to the one-sided fibre product
`R ×_{s, U} U^ν`. -/
def normalizedRelationToPullback {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    overNormalization (finiteComponentsRelation X).left ⟶
      normalizedRelationPullback X :=
  pullback.lift
    (overNormalizationTo (finiteComponentsRelation X).left)
    (overNormalizationMap (finiteComponentsRelation X).s
      (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).s.left))
    (overNormalizationMap_comp (finiteComponentsRelation X).s
      (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).s.left)).symm

/-- The first projection of `R^ν`, the unique lift of the étale projection `t` through
`ν_U`. -/
def normalizedRelationT {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    overNormalization (finiteComponentsRelation X).left ⟶
      overNormalization (finiteComponentsScheme X) :=
  overNormalizationMap (finiteComponentsRelation X).t
    (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).t.left)

/-- The second projection of `R^ν`, the unique lift of the étale projection `s` through
`ν_U`. -/
def normalizedRelationS {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    overNormalization (finiteComponentsRelation X).left ⟶
      overNormalization (finiteComponentsScheme X) :=
  overNormalizationMap (finiteComponentsRelation X).s
    (mapsTo_genericPoints_of_etale (finiteComponentsRelation X).s.left)

/-- The étale equivalence relation `R^ν` on the normalized atlas of `X`, whose source is
the absolute normalization of the kernel pair and whose arrows are the unique lifts of
`t` and `s` through `ν_U`. This is the one-sided fibre product `R ×_U U^ν`, not the
two-sided pullback of `R` along `ν_U`. -/
def normalizedRelation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    PreRelation (overNormalization (finiteComponentsScheme X)) :=
  PreRelation.ofHom (prod.lift (normalizedRelationT X) (normalizedRelationS X))

/-- The source of `normalizedRelation X` is the absolute normalization of the kernel
pair. -/
theorem normalizedRelation_left {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedRelation X).left = overNormalization (finiteComponentsRelation X).left :=
  rfl

/-- The defining map of `normalizedRelation X` is the pair of lifted projections
`(t^ν, s^ν)`. -/
theorem normalizedRelation_hom {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedRelation X).hom = prod.lift (normalizedRelationT X) (normalizedRelationS X) :=
  rfl

/-- The normalized presentation relation of `X` is an étale equivalence relation. -/
instance instIsEtaleEquivalenceRelation_normalizedRelation {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    PreRelation.IsEtaleEquivalenceRelation (normalizedRelation X) :=
  sorry

/-- The two projections of the normalized relation equalize after composing with the
normalized atlas of `X`. -/
theorem normalizedRelation_equalizes {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    yoneda.map (normalizedRelation X).t ≫
        yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫
          finiteComponentsAtlas X =
      yoneda.map (normalizedRelation X).s ≫
        yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫
          finiteComponentsAtlas X :=
  sorry

/-- The canonical atlas of the Type-`u` sheafification of the normalized presentation. -/
def normalizationAtlas {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    yoneda.obj (overNormalization (finiteComponentsScheme X)) ⟶
      sheafifyTypeU (normalizedRelation X).quotientPresheaf :=
  (normalizedRelation X).quotientMk ≫
    toSheafifyTypeU (normalizedRelation X).quotientPresheaf

/-- The normalized atlas of `X` is representable, étale, and surjective onto the
Type-`u` sheafification of the quotient presheaf. -/
theorem normalizationAtlas_presheaf_etaleSurjective {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (MorphismProperty.over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf
      (normalizationAtlas X) :=
  sorry

/-- The absolute normalization `X^ν` of an algebraic space with finitely many irreducible
components on compact opens. -/
def normalization {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] : AlgebraicSpace S :=
  ofEtaleSurjective (sheafifyTypeU_isSheaf (normalizedRelation X).quotientPresheaf)
    (normalizationAtlas X) (normalizationAtlas_presheaf_etaleSurjective X)

/-- The functor of points of `X.normalization` is the Type-`u` fppf sheafification of
the objectwise quotient of the normalized presentation relation. -/
theorem normalization_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.normalization.functorOfPoints =
      sheafifyTypeU (normalizedRelation X).quotientPresheaf :=
  rfl

/-- The canonical absolute normalization morphism `ν_X : X^ν ⟶ X`. -/
def normalizationTo {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.normalization ⟶ X :=
  sheafifyTypeULift
    (PreRelation.quotientPresheafDescTo (normalizedRelation X)
      (yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫ finiteComponentsAtlas X)
      (normalizedRelation_equalizes X))
    X.isSheaf

/-- The sheafification unit of the normalized presentation, postcomposed with `ν_X`,
recovers the normalized atlas of `X`. -/
theorem normalizationTo_comp {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedRelation X).quotientMk ≫
        toSheafifyTypeU (normalizedRelation X).quotientPresheaf ≫ X.normalizationTo =
      yoneda.map (overNormalizationTo (finiteComponentsScheme X)) ≫ finiteComponentsAtlas X :=
  sorry

/-- The algebraic space over `S` represented by the absolute normalization of the
underlying scheme of `T`. -/
def ofOverSchemeNormalization {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    AlgebraicSpace S :=
  ofOver (Over.mk (T.left.normalizationTo ≫ T.hom))

/-- `ofOverSchemeNormalization T` is `ofOver` of the scheme-level absolute
normalization of `T`. -/
theorem ofOverSchemeNormalization_eq {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ofOverSchemeNormalization T =
      ofOver (Over.mk (T.left.normalizationTo ≫ T.hom)) :=
  rfl

/-- The scheme-level absolute normalization morphism of `T`, as a morphism of algebraic
spaces over `S`. -/
def ofOverSchemeNormalizationTo {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ofOverSchemeNormalization T ⟶ ofOver T :=
  ofOverMap (Over.homMk T.left.normalizationTo rfl)

/-- `ofOverSchemeNormalizationTo T` is `ofOverMap` of the scheme-level absolute
normalization morphism of `T`. -/
theorem ofOverSchemeNormalizationTo_eq {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ofOverSchemeNormalizationTo T = ofOverMap (Over.homMk T.left.normalizationTo rfl) :=
  rfl

/-- A morphism of algebraic spaces sends codimension-`0` points to codimension-`0` points. -/
def mapsCodimZero {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  Set.MapsTo (Points.map f) (codimZeroPoints X) (codimZeroPoints Y)

/-- `mapsCodimZero f` means `Points.map f` sends `codimZeroPoints X` into
`codimZeroPoints Y`. -/
theorem mapsCodimZero_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    mapsCodimZero f ↔
      Set.MapsTo (Points.map f) (codimZeroPoints X) (codimZeroPoints Y) :=
  Iff.rfl

/-- A flat morphism of algebraic spaces sends codimension-`0` points to codimension-`0`
points. -/
theorem mapsCodimZero_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] : mapsCodimZero f :=
  Flat.mapsTo_localRingDimAt_eq_zero f

/-- A smooth morphism of algebraic spaces sends codimension-`0` points to
codimension-`0` points. -/
theorem mapsCodimZero_of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] : mapsCodimZero f :=
  mapsCodimZero_of_flat f

/-- An étale morphism of algebraic spaces sends codimension-`0` points to
codimension-`0` points. -/
theorem mapsCodimZero_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] : mapsCodimZero f :=
  mapsCodimZero_of_smooth f

/-- A smooth morphism of algebraic spaces pulls the finite-components-on-compact-opens
property back from the target to the source. -/
theorem HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  HasFiniteIrreducibleComponentsOnCompactOpens.of_flat_locallyOfFiniteType f

/-- An étale morphism of algebraic spaces pulls the finite-components-on-compact-opens
property back from the target to the source. -/
theorem HasFiniteIrreducibleComponentsOnCompactOpens.of_etale
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth f

/-- The absolute normalization of an algebraic space with finitely many irreducible components
on quasi-compact opens is normal. -/
instance instIsNormal_normalization {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsNormal X.normalization :=
  sorry

/-- The absolute normalization morphism of an algebraic space with finitely many irreducible
components on quasi-compact opens is integral. -/
instance instIsIntegralHom_normalizationTo {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsIntegralHom X.normalizationTo :=
  sorry

namespace Normalization

/-- For a scheme with finitely many irreducible components on quasi-compact opens, the
normalization of its represented algebraic space is uniquely isomorphic over that space
to its represented scheme normalization. -/
theorem ofOverIso {S : Scheme.{u}} (T : Over S)
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    ∃! e : (ofOver T).normalization ≅ ofOverSchemeNormalization T,
      e.hom ≫ ofOverSchemeNormalizationTo T = (ofOver T).normalizationTo :=
  sorry

/-- A morphism preserving codimension-zero points between algebraic spaces with finitely
many irreducible components on quasi-compact opens induces a unique morphism of
normalizations commuting with the normalization morphisms. -/
@[stacks 07U4]
theorem existsUnique_map {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] (f : X ⟶ Y)
    (hf : mapsCodimZero f) :
    ∃! g : X.normalization ⟶ Y.normalization,
      g ≫ Y.normalizationTo = X.normalizationTo ≫ f :=
  sorry

/-- A smooth morphism identifies the normalization of its source with the pullback of the
normalization of its target, compatibly with the normalization morphism of its source. -/
theorem existsUnique_pullbackIso_of_smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    :
    -- Local instance justification (proof-local temporary data): the finite-component property derived from smoothness is needed only to form X.normalization in this dependent conclusion.
    letI : HasFiniteIrreducibleComponentsOnCompactOpens X :=
      HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth f
    ∃! e : X.normalization ≅ pullback Y.normalizationTo f,
      e.hom ≫ pullback.snd Y.normalizationTo f = X.normalizationTo :=
  sorry

/-- A smooth morphism pulls back the finite-component property, preserves codimension-zero
points, and identifies the normalization of its source with the pullback of the
normalization of its target. The first projection of the comparison satisfies the
normalization-map equation by the pullback condition, so it is the unique induced
map of normalizations. -/
theorem existsUnique_pullbackIso_of_smooth_with_mapsTo
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Smooth f] [HasFiniteIrreducibleComponentsOnCompactOpens Y] :
    -- Local instance justification (proof-local temporary data): the finite-component property derived from smoothness is needed only to form X.normalization in this dependent conclusion.
    letI : HasFiniteIrreducibleComponentsOnCompactOpens X :=
      HasFiniteIrreducibleComponentsOnCompactOpens.of_smooth f
    mapsCodimZero f ∧ ∃! e : X.normalization ≅ pullback Y.normalizationTo f,
      e.hom ≫ pullback.snd Y.normalizationTo f = X.normalizationTo := by
  exact ⟨mapsCodimZero_of_smooth f, existsUnique_pullbackIso_of_smooth f⟩

end Normalization

end AlgebraicGeometry.AlgebraicSpace
