/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability

/-!
# Quotients of affine finite locally free groupoid schemes

This module constructs the invariant spectrum over the base scheme and records its
kernel-pair and fppf quotient properties.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The structure morphism of the object scheme is constant on the fibres of the
invariant-spectrum map. -/
theorem invariantSpectrumMap_respectsBase {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] :
    ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom := sorry

/-- The descended structure morphism from the invariant spectrum to the base scheme. -/
noncomputable def invariantSpectrumStructureMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) :
    Spec (CommRingCat.of (tSharp.eqLocus (algebraMap A B))) ⟶ S :=
  @EffectiveEpi.desc _ _ _ _ _ (invariantSpectrumMap G tSharp eU)
    h_effective G.U.hom h_respects

/-- Pulling the descended invariant-spectrum structure morphism back along the canonical
map recovers the original structure morphism. -/
theorem invariantSpectrumStructureMap_fac {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) :
    invariantSpectrumMap G tSharp eU ≫
        invariantSpectrumStructureMap G tSharp eU h_effective h_respects = G.U.hom := sorry

/-- The descended structure morphism is uniquely determined by its pullback along the
invariant-spectrum map. -/
theorem invariantSpectrumStructureMap_unique {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom)
    (p : Spec (CommRingCat.of (tSharp.eqLocus (algebraMap A B))) ⟶ S)
    (hp : invariantSpectrumMap G tSharp eU ≫ p = G.U.hom) :
    p = invariantSpectrumStructureMap G tSharp eU h_effective h_respects := sorry

/-- The spectrum of the invariant equalizer ring, equipped with its descended morphism to
the base scheme. -/
def invariantSpectrumOver {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) : Over S :=
  Over.mk (invariantSpectrumStructureMap G tSharp eU h_effective h_respects)

/-- The underlying scheme of the invariant spectrum over the base is the spectrum of the
invariant equalizer ring. -/
theorem invariantSpectrumOver_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) :
    (invariantSpectrumOver G tSharp eU h_effective h_respects).left =
      Spec (CommRingCat.of (tSharp.eqLocus (algebraMap A B))) := sorry

/-- The structure morphism of the invariant spectrum over the base is its descended
structure morphism. -/
theorem invariantSpectrumOver_hom {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) :
    (invariantSpectrumOver G tSharp eU h_effective h_respects).hom =
      invariantSpectrumStructureMap G tSharp eU h_effective h_respects := sorry

/-- The invariant-spectrum map regarded as a morphism over the base scheme. -/
def invariantSpectrumQuotientMap {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) :
    G.U ⟶ invariantSpectrumOver G tSharp eU h_effective h_respects :=
  Over.homMk (invariantSpectrumMap G tSharp eU)
    (invariantSpectrumStructureMap_fac G tSharp eU h_effective h_respects)

/-- The underlying scheme map of the invariant-spectrum quotient morphism is the canonical
map to the invariant spectrum. -/
theorem invariantSpectrumQuotientMap_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) :
    (invariantSpectrumQuotientMap G tSharp eU h_effective h_respects).left =
      invariantSpectrumMap G tSharp eU := sorry

/-- The invariant-spectrum quotient morphism equalizes the target and source maps. -/
theorem invariantSpectrumQuotientMap_equalizes {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left)
    (h_effective : EffectiveEpi (invariantSpectrumMap G tSharp eU))
    (h_respects : ∀ {T : Scheme.{u}} (f g : T ⟶ G.U.left),
      f ≫ invariantSpectrumMap G tSharp eU =
          g ≫ invariantSpectrumMap G tSharp eU →
        f ≫ G.U.hom = g ≫ G.U.hom) :
    G.toPreRelation.t ≫
        invariantSpectrumQuotientMap G tSharp eU h_effective h_respects =
      G.toPreRelation.s ≫
        invariantSpectrumQuotientMap G tSharp eU h_effective h_respects := sorry

/-- The canonical morphism from an affine finite locally free equivalence relation to the
kernel pair of its invariant-spectrum quotient is an isomorphism. -/
@[instance]
theorem invariantKernelPairComparison_isIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] :
    IsIso (G.toPreRelation.kernelPairLift
      (invariantSpectrumQuotientMap G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))
      (invariantSpectrumQuotientMap_equalizes G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))) := sorry

/-- The invariant spectrum represents the quotient sheaf of an affine finite locally free
equivalence-relation groupoid in the fppf topology over the base scheme. -/
@[instance]
theorem invariantQuotientComparison_fppf_isIso {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    [IsEquivalenceRelation G.t G.s] :
    IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
      (StandardTopology.fppf.overTopology S)
      (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
      (invariantSpectrumQuotientMap G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))
      (invariantSpectrumQuotientMap_equalizes G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))) := sorry

end AlgebraicGeometry.GroupoidScheme
