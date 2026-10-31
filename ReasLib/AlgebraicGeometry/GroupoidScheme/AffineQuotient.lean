/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical

/-!
# Affine quotients of finite locally free groupoid schemes

The spectrum of invariant global functions carries the canonical quotient map and
represents the fppf quotient of an affine finite locally free equivalence relation.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

set_option backward.isDefEq.respectTransparency false in
/-- A groupoid scheme with monic `(t, s)` is an internal equivalence relation. -/
theorem isEquivalenceRelation_of_mono {S : Scheme.{u}} (P : GroupoidScheme S)
    [Mono P.toPreRelation.hom.left] : IsEquivalenceRelation P.t P.s := by
  letI : Mono (prod.lift P.t P.s) :=
    Over.mono_of_mono_left P.toPreRelation.hom
  refine ⟨⟨{
    right_cancellation := ?_
    r := P.e
    reflexivity₁ := P.identity_target
    reflexivity₂ := P.identity_source
    s := P.i
    symmetry₁ := P.inverse_target
    symmetry₂ := P.inverse_source
    c := pullback.cone P.s P.t
    isLimit := pullback.isLimit P.s P.t
    t := P.c
    transitivity₁ := P.comp_target
    transitivity₂ := P.comp_source
  }⟩⟩
  intro T f g ht hs
  apply (cancel_mono (prod.lift P.t P.s)).mp
  apply prod.hom_ext
  · simpa only [Category.assoc, prod.lift_fst] using ht
  · simpa only [Category.assoc, prod.lift_snd] using hs

/-- The ring homomorphism on global sections induced by the target map. -/
def objectQuotientTargetHom {S : Scheme.{u}} (P : GroupoidScheme S) :
    (Γ(P.U.left, ⊤) : Type u) →+* (Γ(P.R.left, ⊤) : Type u) :=
  CommRingCat.Hom.hom P.t.left.appTop

/-- The spectrum of global functions equalized by the target and source maps. -/
def objectQuotient {S : Scheme.{u}} (P : GroupoidScheme S) : Scheme.{u} :=
  Spec (CommRingCat.of ((objectQuotientTargetHom P).eqLocus
    (CommRingCat.Hom.hom P.s.left.appTop)))

/-- The object quotient is the spectrum of the invariant equalizer subring. -/
theorem objectQuotient_eq {S : Scheme.{u}} (P : GroupoidScheme S) :
    objectQuotient P = Spec (CommRingCat.of ((objectQuotientTargetHom P).eqLocus
      (CommRingCat.Hom.hom P.s.left.appTop))) := rfl

/-- The canonical projection to the spectrum of invariant global functions. -/
def objectQuotientProjection {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] : P.U.left ⟶ objectQuotient P :=
  P.U.left.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom ((objectQuotientTargetHom P).eqLocus
      (CommRingCat.Hom.hom P.s.left.appTop)).subtype)

/-- The structure morphism to the base is constant on the fibres of the canonical
invariant-spectrum projection. -/
theorem objectQuotientProjection_respectsBase {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    ∀ {T : Scheme.{u}} (f g : T ⟶ P.U.left),
      f ≫ objectQuotientProjection P = g ≫ objectQuotientProjection P →
        f ≫ P.U.hom = g ≫ P.U.hom := by
  let sourceAlgebra := (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra
  let objectPresentation := P.U.left.isoSpec.symm
  let arrowAffine := isAffine_of_isAffineHom P.s.left
  let arrowPresentation := (@Scheme.isoSpec P.R.left arrowAffine).symm
  let sourceCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.s.left).symm
  let targetCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.t.left).symm
  letI : IsEquivalenceRelation P.t P.s := isEquivalenceRelation_of_mono P
  have hmap : objectQuotientProjection P = invariantSpectrumMap P
      (objectQuotientTargetHom P) objectPresentation := by rfl
  rw [hmap]
  exact @invariantSpectrumMap_respectsBase _ P _ _ _ _ sourceAlgebra
    (objectQuotientTargetHom P) objectPresentation arrowPresentation
    sourceCompatibility targetCompatibility inferInstance inferInstance inferInstance

/-- The canonical invariant-spectrum projection of an affine finite locally free
equivalence-relation groupoid is an effective epimorphism. -/
theorem objectQuotientProjection_effectiveEpi {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : EffectiveEpi (objectQuotientProjection P) :=
  let sourceAlgebra := (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra
  let objectPresentation := P.U.left.isoSpec.symm
  let arrowAffine := isAffine_of_isAffineHom P.s.left
  let arrowPresentation := (@Scheme.isoSpec P.R.left arrowAffine).symm
  let sourceCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.s.left).symm
  let targetCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.t.left).symm
  let finiteLocallyFree := @invariantSpectrumMap_isFiniteLocallyFree _ P _ _ _ _ sourceAlgebra
    (objectQuotientTargetHom P) objectPresentation arrowPresentation
    sourceCompatibility targetCompatibility inferInstance inferInstance
    (isEquivalenceRelation_of_mono P)
  let surjective := @invariantSpectrumMap_surjective _ P _ _ _ _ sourceAlgebra
    (objectQuotientTargetHom P) objectPresentation arrowPresentation
    sourceCompatibility targetCompatibility inferInstance inferInstance
  (isRegularEpi_iff_effectiveEpi (objectQuotientProjection P)).mp
    (@isRegularEpi_of_flat_of_surjective_of_isAffine _ _ inferInstance (isAffine_Spec _)
      (objectQuotientProjection P) ⟨surjective⟩ finiteLocallyFree.flat)

/-- The invariant spectrum, equipped with its descended morphism to the base scheme. -/
def objectQuotientOver {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : Over S :=
  Over.mk (@EffectiveEpi.desc _ _ _ _ _ (objectQuotientProjection P)
    (objectQuotientProjection_effectiveEpi P) P.U.hom
    (objectQuotientProjection_respectsBase P))

/-- The underlying scheme of the quotient over the base is the invariant spectrum. -/
theorem objectQuotientOver_left {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    (objectQuotientOver P).left = objectQuotient P := rfl

/-- The canonical invariant-spectrum quotient morphism over the base scheme. -/
def objectQuotientMap {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : P.U ⟶ objectQuotientOver P :=
  Over.homMk (objectQuotientProjection P)
    (@EffectiveEpi.fac _ _ _ _ _ (objectQuotientProjection P)
      (objectQuotientProjection_effectiveEpi P) P.U.hom
      (objectQuotientProjection_respectsBase P))

/-- The underlying quotient morphism is the spectrum map of the invariant-ring inclusion,
transported through the canonical affine presentation of the object scheme. -/
theorem objectQuotientMap_left {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    (objectQuotientMap P).left = P.U.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom ((objectQuotientTargetHom P).eqLocus
        (CommRingCat.Hom.hom P.s.left.appTop)).subtype) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The quotient morphism equalizes the target and source maps. -/
theorem objectQuotientMap_equalizes {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    P.toPreRelation.t ≫ objectQuotientMap P =
      P.toPreRelation.s ≫ objectQuotientMap P := by
  have ht : P.toPreRelation.t = P.t := by
    exact prod.lift_fst P.t P.s
  have hs : P.toPreRelation.s = P.s := by
    exact prod.lift_snd P.t P.s
  rw [ht, hs]
  apply Over.OverMorphism.ext
  change P.t.left ≫ objectQuotientProjection P = P.s.left ≫ objectQuotientProjection P
  letI : IsAffine P.R.left := isAffine_of_isAffineHom P.s.left
  unfold objectQuotientProjection
  rw [← Category.assoc, ← Scheme.isoSpec_hom_naturality,
    ← Category.assoc, ← Scheme.isoSpec_hom_naturality]
  rw [Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  exact x.property

/-- The canonical comparison from the fppf quotient sheaf to the represented
invariant spectrum over the base scheme. -/
def objectQuotientSheafComparison {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :=
  @Scheme.PreRelation.quotientSheafDesc _ _ _ P.toPreRelation
    (StandardTopology.fppf.overTopology S)
    (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
    (objectQuotientMap P) (objectQuotientMap_equalizes P)

/-- The quotient morphism is finite locally free. -/
theorem objectQuotientMap_isFiniteLocallyFree {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    IsFiniteLocallyFree (objectQuotientMap P).left := by
  let sourceAlgebra := (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra
  let arrowAffine := isAffine_of_isAffineHom P.s.left
  exact @invariantSpectrumMap_isFiniteLocallyFree _ P _ _ _ _ sourceAlgebra
    (objectQuotientTargetHom P) P.U.left.isoSpec.symm
    (@Scheme.isoSpec P.R.left arrowAffine).symm
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.s.left).symm
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.t.left).symm
    inferInstance inferInstance (isEquivalenceRelation_of_mono P)

/-- The canonical `(t, s)` comparison identifies the arrow scheme with the kernel
pair of the quotient morphism. -/
theorem objectQuotient_kernelPair_isIso {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    IsIso (P.toPreRelation.kernelPairLift (objectQuotientMap P)
      (objectQuotientMap_equalizes P)) := by
  let sourceAlgebra := (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra
  let objectPresentation := P.U.left.isoSpec.symm
  let arrowAffine := isAffine_of_isAffineHom P.s.left
  let arrowPresentation := (@Scheme.isoSpec P.R.left arrowAffine).symm
  let sourceCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.s.left).symm
  let targetCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.t.left).symm
  letI : IsEquivalenceRelation P.t P.s := isEquivalenceRelation_of_mono P
  exact invariantKernelPairComparison_isIso P (objectQuotientTargetHom P)
    objectPresentation arrowPresentation sourceCompatibility targetCompatibility

/-- The quotient morphism transported to an identified object scheme. -/
def quotientMapOf {S : Scheme.{u}} {G P : GroupoidScheme S} (hU : P.U = G.U)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] : G.U ⟶ objectQuotientOver P :=
  eqToHom hU.symm ≫ objectQuotientMap P

/-- The transported quotient morphism is the composite of the equality-induced
identification and the canonical quotient morphism. -/
theorem quotientMapOf_spec {S : Scheme.{u}} {G P : GroupoidScheme S}
    (hU : P.U = G.U) [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left]
    [IsFiniteLocallyFree P.t.left] [Mono P.toPreRelation.hom.left] :
    quotientMapOf hU = eqToHom hU.symm ≫ objectQuotientMap P := rfl

/-- The invariant spectrum is affine and represents the fppf quotient sheaf. -/
theorem objectQuotient_represents {S : Scheme.{u}} (P : GroupoidScheme S)
    [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
    [Mono P.toPreRelation.hom.left] :
    IsAffine (objectQuotient P) ∧ IsIso (objectQuotientSheafComparison P) := by
  let sourceAlgebra := (CommRingCat.Hom.hom P.s.left.appTop).toAlgebra
  let objectPresentation := P.U.left.isoSpec.symm
  let arrowAffine := isAffine_of_isAffineHom P.s.left
  let arrowPresentation := (@Scheme.isoSpec P.R.left arrowAffine).symm
  let sourceCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.s.left).symm
  let targetCompatibility :=
    (@Scheme.isoSpec_inv_naturality _ _ arrowAffine inferInstance P.t.left).symm
  letI : IsEquivalenceRelation P.t P.s := isEquivalenceRelation_of_mono P
  refine ⟨by change IsAffine (Spec _); infer_instance, ?_⟩
  letI : (StandardTopology.fppf.overTopology S).Subcanonical :=
    StandardTopology.overTopologySubcanonical StandardTopology.fppf S
  exact invariantQuotientComparison_fppf_isIso P (objectQuotientTargetHom P)
    objectPresentation arrowPresentation sourceCompatibility targetCompatibility

/-- Equality-induced transport of the quotient morphism preserves finite local freeness. -/
theorem quotientMapOf_isFiniteLocallyFree {S : Scheme.{u}} {G P : GroupoidScheme S}
    (hU : P.U = G.U) [IsAffine P.U.left] [IsFiniteLocallyFree P.s.left]
    [IsFiniteLocallyFree P.t.left] [Mono P.toPreRelation.hom.left] :
    IsFiniteLocallyFree (quotientMapOf hU).left := by
  change IsFiniteLocallyFree ((eqToHom hU.symm).left ≫ (objectQuotientMap P).left)
  have hi : IsIso (eqToHom hU.symm).left :=
    (Over.forget S).map_isIso (eqToHom hU.symm)
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsFiniteLocallyFree)
    (eqToHom hU.symm).left (objectQuotientMap P).left).2 (objectQuotientMap_isFiniteLocallyFree P)

end AlgebraicGeometry.GroupoidScheme
