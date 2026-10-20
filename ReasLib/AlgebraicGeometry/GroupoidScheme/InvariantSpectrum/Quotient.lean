/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.SingletonCover

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

section KernelPair

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
  (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
  (h_source : eR.hom ≫ G.s.left =
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
  (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
  [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
  [IsEquivalenceRelation G.t G.s]

/-- The invariant-spectrum quotient morphism of an explicitly presented affine groupoid,
with its canonical effective-epimorphism and base-compatibility proofs. -/
abbrev invariantSpectrumQuotient :
    G.U ⟶ invariantSpectrumOver G tSharp eU
      (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
      (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target) :=
  invariantSpectrumQuotientMap G tSharp eU
    (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
    (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target)

/-- The underlying kernel-pair comparison is flat. -/
theorem invariantKernelPairComparison_flat :
    Flat (G.toPreRelation.kernelPairLift
      (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
      (invariantSpectrumQuotientMap_equalizes G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))).left := sorry

/-- The underlying kernel-pair comparison is surjective. -/
theorem invariantKernelPairComparison_surjective :
    Surjective (G.toPreRelation.kernelPairLift
      (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
      (invariantSpectrumQuotientMap_equalizes G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))).left := sorry

/-- The underlying kernel-pair comparison is a monomorphism. -/
theorem invariantKernelPairComparison_mono :
    Mono (G.toPreRelation.kernelPairLift
      (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
      (invariantSpectrumQuotientMap_equalizes G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))).left := sorry

/-- The arrow scheme is the kernel pair of the invariant-spectrum quotient. The inverse
is obtained by descending the identity of the affine arrow scheme along the flat, surjective
kernel-pair comparison. -/
def invariantKernelPairIso :
    G.R ≅ Limits.pullback (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
      (invariantSpectrumQuotient G tSharp eU eR h_source h_target) :=
  let q := invariantSpectrumQuotient G tSharp eU eR h_source h_target
  let comparison := G.toPreRelation.kernelPairLift q
    (invariantSpectrumQuotientMap_equalizes G tSharp eU
      (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
      (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))
  let objectAffine := IsAffine.of_isIso eU.inv
  let arrowAffine := IsAffine.of_isIso eR.inv
  let affineMap : IsAffineHom q.left :=
    @isAffineHom_of_isAffine _ _ q.left objectAffine (isAffine_Spec _)
  let affinePullback : IsAffine (Limits.pullback q.left q.left) :=
    @IsAffine.of_isPullback _ _ _ _ _ _ _ _ objectAffine affineMap
      (IsPullback.of_hasPullback q.left q.left)
  let pairAffine : IsAffine (Limits.pullback q q).left :=
    @IsAffine.of_isIso _ _ (PreservesPullback.iso (Over.forget S) q q).hom
      inferInstance affinePullback
  let regular := @isRegularEpi_of_flat_of_surjective_of_isAffine _ _
    arrowAffine pairAffine comparison.left
    (invariantKernelPairComparison_surjective G tSharp eU eR h_source h_target)
    (invariantKernelPairComparison_flat G tSharp eU eR h_source h_target)
  let monic := invariantKernelPairComparison_mono G tSharp eU eR h_source h_target
  { hom := comparison
    inv := Over.homMk
      (@IsRegularEpi.desc _ _ _ _ _ comparison.left regular (𝟙 G.R.left) (by
        exact congrArg (fun f ↦ f ≫ 𝟙 G.R.left)
          (monic.right_cancellation _ _ (@IsRegularEpi.w _ _ _ _ comparison.left regular))))
      (by sorry)
    hom_inv_id := by sorry
    inv_hom_id := by sorry }

/-- The forward map of the invariant kernel-pair isomorphism is the canonical comparison. -/
theorem invariantKernelPairIso_hom :
    (invariantKernelPairIso G tSharp eU eR h_source h_target).hom =
      G.toPreRelation.kernelPairLift
        (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
        (invariantSpectrumQuotientMap_equalizes G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target)) := rfl

/-- The inverse kernel-pair comparison followed by the target map is the first projection. -/
theorem invariantKernelPairIso_inv_t :
    (invariantKernelPairIso G tSharp eU eR h_source h_target).inv ≫ G.t =
      pullback.fst (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
        (invariantSpectrumQuotient G tSharp eU eR h_source h_target) := sorry

/-- The inverse kernel-pair comparison followed by the source map is the second projection. -/
theorem invariantKernelPairIso_inv_s :
    (invariantKernelPairIso G tSharp eU eR h_source h_target).inv ≫ G.s =
      pullback.snd (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
        (invariantSpectrumQuotient G tSharp eU eR h_source h_target) := sorry

end KernelPair

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
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))) :=
  (invariantKernelPairIso G tSharp eU eR h_source h_target).isIso_hom

section InvariantSpectrum

variable {S : Scheme.{u}} (G : GroupoidScheme S)
  {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
  (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
  (h_source : eR.hom ≫ G.s.left =
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
  (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
  [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
  [IsEquivalenceRelation G.t G.s]

-- Local instance justification (search instability): the fppf over-topology's
-- subcanonical structure must be passed explicitly to sheaf Yoneda constructions.
/-- The fppf topology on `Over S` is subcanonical; the global instance is not found by
instance search for the `fppf` topology, so it is registered locally here. -/
local instance : (StandardTopology.fppf.overTopology S).Subcanonical :=
  StandardTopology.overTopologySubcanonical StandardTopology.fppf S

/-- Two points of the object scheme with the same image in the invariant spectrum are related
by the groupoid. -/
theorem invariantSpectrumQuotient_pointRel {W : Over S} (a b : W ⟶ G.U)
    (h : a ≫ invariantSpectrumQuotient G tSharp eU eR h_source h_target =
      b ≫ invariantSpectrumQuotient G tSharp eU eR h_source h_target) :
    G.toPreRelation.pointRel W a b := sorry

/-- The invariant-spectrum quotient morphism generates an fppf covering sieve. -/
theorem invariantSpectrumQuotient_generate_mem_fppf :
    Sieve.generate (Presieve.singleton
        (invariantSpectrumQuotient G tSharp eU eR h_source h_target)) ∈
      StandardTopology.fppf.overTopology S (invariantSpectrumOver G tSharp eU
        (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target)) :=
  have : IsFiniteLocallyFree
      (invariantSpectrumQuotient G tSharp eU eR h_source h_target).left :=
    invariantSpectrumMap_isFiniteLocallyFree G tSharp eU eR h_source h_target
  have : Surjective (invariantSpectrumQuotient G tSharp eU eR h_source h_target).left :=
    ⟨invariantSpectrumMap_surjective G tSharp eU eR h_source h_target⟩
  Scheme.PreRelation.generate_singleton_mem_fppf_over
    (invariantSpectrumQuotient G tSharp eU eR h_source h_target)

/-- The inverse comparison from the represented invariant spectrum to the fppf quotient sheaf,
classified by the descent of the quotient class of `𝟙 U`. -/
def invariantQuotientSheafInverse :
    (StandardTopology.fppf.overTopology S).uliftYoneda.{u + 1}.obj
        (invariantSpectrumOver G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target)) ⟶
      G.toPreRelation.quotientSheaf (StandardTopology.fppf.overTopology S) :=
  @Scheme.PreRelation.quotientSheafInvOfCover _ _ _ (StandardTopology.fppf.overTopology S)
    (StandardTopology.overTopologySubcanonical StandardTopology.fppf S) G.toPreRelation
    (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
    (invariantSpectrumQuotient_generate_mem_fppf G tSharp eU eR h_source h_target)
    (fun a b h ↦ invariantSpectrumQuotient_pointRel G tSharp eU eR h_source h_target a b h)

/-- The invariant spectrum represents the fppf quotient sheaf (Stacks 03BM): the canonical
comparison and the descended inverse form an explicit isomorphism. -/
def invariantQuotientSheafIso :
    G.toPreRelation.quotientSheaf (StandardTopology.fppf.overTopology S) ≅
      (StandardTopology.fppf.overTopology S).uliftYoneda.{u + 1}.obj
        (invariantSpectrumOver G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target)) :=
  @Scheme.PreRelation.quotientSheafIsoOfCover _ _ _ (StandardTopology.fppf.overTopology S)
    (StandardTopology.overTopologySubcanonical StandardTopology.fppf S) G.toPreRelation
    (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
    (invariantSpectrumQuotientMap_equalizes G tSharp eU
      (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
      (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))
    (invariantSpectrumQuotient_generate_mem_fppf G tSharp eU eR h_source h_target)
    (fun a b h ↦ invariantSpectrumQuotient_pointRel G tSharp eU eR h_source h_target a b h)

/-- The forward map of `invariantQuotientSheafIso` is the canonical comparison
`quotientSheafDesc` of the invariant-spectrum quotient morphism. -/
theorem invariantQuotientSheafIso_hom :
    (invariantQuotientSheafIso G tSharp eU eR h_source h_target).hom =
      @Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
        (StandardTopology.fppf.overTopology S)
        (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
        (invariantSpectrumQuotient G tSharp eU eR h_source h_target)
        (invariantSpectrumQuotientMap_equalizes G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target)) :=
  rfl

/-- The inverse map of `invariantQuotientSheafIso` is the descended comparison. -/
theorem invariantQuotientSheafIso_inv :
    (invariantQuotientSheafIso G tSharp eU eR h_source h_target).inv =
      invariantQuotientSheafInverse G tSharp eU eR h_source h_target :=
  rfl

end InvariantSpectrum

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
        (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))) :=
  (invariantQuotientSheafIso G tSharp eU eR h_source h_target).isIso_hom

end AlgebraicGeometry.GroupoidScheme
