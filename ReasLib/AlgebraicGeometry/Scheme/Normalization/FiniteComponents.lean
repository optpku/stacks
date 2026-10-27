/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Components
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.CompactOpens
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Reduction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normalization and finite irreducible components

This file records decomposition, generic-point behavior, factorization, and lifting results for
relative and absolute normalizations under finite irreducible-component hypotheses.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

private theorem isNormalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsNormalRing R] (e : R ≃+* S) : IsNormalRing S := by
  have hloc (p : PrimeSpectrum S) :
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
    let q : Ideal R := p.asIdeal.comap e.toRingHom
    haveI : q.IsPrime := inferInstance
    let h : Localization.AtPrime q ≃+* Localization.AtPrime p.asIdeal :=
      IsLocalization.ringEquivOfRingEquiv (M := q.primeCompl)
        (T := p.asIdeal.primeCompl) _ _ e (e.map_primeCompl_comap_eq p.asIdeal)
    exact ⟨h.symm.injective.isDomain h.symm.toRingHom, IsIntegrallyClosed.of_equiv h⟩
  exact ⟨fun p ↦ (hloc p).1, fun p ↦ (hloc p).2⟩

/-- The relative normalization of a quasi-compact and quasi-separated morphism from a normal
scheme with finitely many irreducible components on quasi-compact opens admits a pairwise disjoint
open cover by normal integral schemes. -/
theorem normalization_hasPairwiseDisjointOpenCoverByNormalIntegral_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    f.normalization.HasPairwiseDisjointOpenCoverByNormalIntegral := sorry

/-- The relative normalization of a quasi-compact and quasi-separated morphism from a normal
scheme with finitely many irreducible components on quasi-compact opens is normal. -/
theorem normalization_isNormal_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    f.normalization.isNormal := by
  obtain ⟨ι, U, hcover, _, hnormal⟩ :=
    f.normalization_hasPairwiseDisjointOpenCoverByNormalIntegral_of_isNormal hY
  intro x
  obtain ⟨i, hix⟩ := hcover.exists_mem x
  let y : (U i).toScheme := ⟨x, hix⟩
  haveI : IsNormalRing ((U i).toScheme.presheaf.stalk y) := (hnormal i).2 y
  exact isNormalRing_of_ringEquiv
    (asIso ((U i).ι.stalkMap y)).commRingCatIsoToRingEquiv.symm

/-- The canonical map to the relative normalization of a quasi-compact and quasi-separated
morphism from a normal scheme with finitely many irreducible components on quasi-compact opens
bijects the generic points of its source and target. -/
theorem bijOn_genericPoints_toNormalization_of_isNormal
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (hY : Y.isNormal) :
    Set.BijOn f.toNormalization (genericPoints Y) (genericPoints f.normalization) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

namespace Normalization

private theorem genericPointSpectrumCoproduct_isLocallyNoetherian (X : Scheme.{u}) :
    IsLocallyNoetherian (genericPointSpectrumCoproduct X) := by
  exact (isLocallyNoetherian_iff_openCover
    (sigmaOpenCover (fun η : genericPoints X ↦ Spec (X.residueField η.1)))).mpr
    (fun i ↦ by change IsLocallyNoetherian (Spec (X.residueField i.1)); infer_instance)

private theorem genericPointSpectrumCoproduct_isNormal (X : Scheme.{u}) :
    (genericPointSpectrumCoproduct X).isNormal := by
  intro x
  obtain ⟨⟨i, y⟩, rfl⟩ :=
    (sigmaMk (fun η : genericPoints X ↦ Spec (X.residueField η.1))).surjective x
  simp only [sigmaMk_mk]
  change IsNormalRing ((genericPointSpectrumCoproduct X).presheaf.stalk
    (Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) i y))
  have hy : y ∈ genericPoints (Spec (X.residueField i.1)) := by
    rw [genericPoints_eq_singleton (α := Spec (X.residueField i.1))]
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  haveI : _root_.IsReduced (X.residueField i.1) := isReduced_of_noZeroDivisors
  have hf : IsField ((Spec (X.residueField i.1)).presheaf.stalk y) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ y hy
  haveI : IsOpenImmersion
      (Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) i) := by
    change IsOpenImmersion
      ((sigmaOpenCover (fun η : genericPoints X ↦ Spec (X.residueField η.1))).f i)
    infer_instance
  have hg : IsField ((genericPointSpectrumCoproduct X).presheaf.stalk
      (Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) i y)) :=
    (asIso
      ((Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) i).stalkMap y)).commRingCatIsoToRingEquiv.isField hf
  letI := hg.toField
  infer_instance

private theorem genericPointSpectrumCoproductTo_bijOn (X : Scheme.{u}) :
    Set.BijOn (genericPointSpectrumCoproductTo X)
      (genericPoints (genericPointSpectrumCoproduct X)) (genericPoints X) := by
  have hpoints : genericPoints (genericPointSpectrumCoproduct X) = Set.univ := by
    letI : DiscreteTopology (genericPointSpectrumCoproduct X) :=
      (sigmaMk (fun η : genericPoints X ↦ Spec (X.residueField η.1))).discreteTopology
    apply Set.eq_univ_of_forall
    intro x
    change closure {x} ∈ irreducibleComponents (genericPointSpectrumCoproduct X)
    rw [isClosed_singleton.closure_eq]
    refine ⟨isIrreducible_singleton, ?_⟩
    intro S hS hxS y hy
    exact Set.mem_singleton_iff.mpr (hS.2.subsingleton hy (hxS (Set.mem_singleton x)))
  have happly (η : genericPoints X) (p : Spec (X.residueField η.1)) :
      genericPointSpectrumCoproductTo X
        (Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) η p) = η.1 := by
    change (Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) η ≫
      genericPointSpectrumCoproductTo X) p = η.1
    rw [genericPointSpectrumCoproductTo_ι]
    exact X.fromSpecResidueField_apply η.1 p
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨⟨i, a⟩, rfl⟩ :=
      (sigmaMk (fun η : genericPoints X ↦ Spec (X.residueField η.1))).surjective a
    simpa only [sigmaMk_mk, happly] using i.2
  · intro a ha b hb hab
    obtain ⟨⟨i, a⟩, rfl⟩ :=
      (sigmaMk (fun η : genericPoints X ↦ Spec (X.residueField η.1))).surjective a
    obtain ⟨⟨j, b⟩, rfl⟩ :=
      (sigmaMk (fun η : genericPoints X ↦ Spec (X.residueField η.1))).surjective b
    have hij : i = j := Subtype.ext (by
      simpa only [sigmaMk_mk, happly] using hab)
    subst j
    congr 1
    exact congrArg (fun p ↦ Sigma.mk i p) (Subsingleton.elim a b)
  · intro x hx
    let η : genericPoints X := ⟨x, hx⟩
    let p : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
    refine ⟨Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) η p,
      ?_, happly η p⟩
    rw [hpoints]
    trivial

/-- The normalization of a scheme with finitely many irreducible components on quasi-compact
opens admits a pairwise disjoint open cover by normal integral schemes. -/
@[stacks 035Q]
theorem cover
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    X.normalization.HasPairwiseDisjointOpenCoverByNormalIntegral := by
  haveI : IsLocallyNoetherian (genericPointSpectrumCoproduct X) :=
    genericPointSpectrumCoproduct_isLocallyNoetherian X
  exact Hom.normalization_hasPairwiseDisjointOpenCoverByNormalIntegral_of_isNormal
    (genericPointSpectrumCoproductTo X) (genericPointSpectrumCoproduct_isNormal X)

/-- The normalization morphism of a scheme with finitely many irreducible components on
quasi-compact opens bijects the generic points of its source and target. -/
@[stacks 035Q]
theorem bijOn_genericPoints
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Set.BijOn X.normalizationTo (genericPoints X.normalization) (genericPoints X) := by
  haveI : IsLocallyNoetherian (genericPointSpectrumCoproduct X) :=
    genericPointSpectrumCoproduct_isLocallyNoetherian X
  have hrel := Hom.bijOn_genericPoints_toNormalization_of_isNormal
    (genericPointSpectrumCoproductTo X) (genericPointSpectrumCoproduct_isNormal X)
  have hcomp : Set.BijOn
      (X.normalizationTo ∘ (genericPointSpectrumCoproductTo X).toNormalization)
      (genericPoints (genericPointSpectrumCoproduct X)) (genericPoints X) := by
    change Set.BijOn ((genericPointSpectrumCoproductTo X).toNormalization ≫
      (genericPointSpectrumCoproductTo X).fromNormalization) _ _
    rw [Hom.toNormalization_fromNormalization]
    exact genericPointSpectrumCoproductTo_bijOn X
  have h := (Set.bijOn_comp_iff hrel.injOn).mp hcomp
  simpa only [hrel.image_eq] using h

/-- The normalization morphism of a scheme with finitely many irreducible components on
quasi-compact opens is surjective. -/
@[stacks 035Q]
theorem surjective
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Surjective X.normalizationTo := by
  have hgeneric : genericPoints X ⊆ Set.range X.normalizationTo := by
    intro x hx
    let η : genericPoints X := ⟨x, hx⟩
    let p : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
    let y := Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) η p
    refine ⟨(genericPointSpectrumCoproductTo X).toNormalization y, ?_⟩
    change ((genericPointSpectrumCoproductTo X).toNormalization ≫
      (genericPointSpectrumCoproductTo X).fromNormalization) y = x
    rw [Scheme.Hom.toNormalization_fromNormalization]
    change (Limits.Sigma.ι (fun η : genericPoints X ↦ Spec (X.residueField η.1)) η ≫
      genericPointSpectrumCoproductTo X) p = x
    rw [genericPointSpectrumCoproductTo_ι]
    exact X.fromSpecResidueField_apply x p
  haveI : IsDominant X.normalizationTo := ⟨by
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← genericPoints.closure]
    exact closure_mono hgeneric⟩
  infer_instance

/-- The normalization morphism of a reduced scheme with finitely many irreducible components is
birational. -/
theorem isBirational_of_isReduced_finiteComponents
    (X : Scheme.{u}) [IsReduced X] [Finite (irreducibleComponents X)] :
    IsBirational X.normalizationTo := by
  haveI : IsLocallyNoetherian (genericPointSpectrumCoproduct X) :=
    genericPointSpectrumCoproduct_isLocallyNoetherian X
  haveI : ∀ i : genericPoints X,
      IsReduced ((sigmaOpenCover (fun η : genericPoints X ↦ Spec (X.residueField η.1))).X i) :=
    fun i ↦ by
      haveI : _root_.IsReduced (X.residueField i.1) := isReduced_of_noZeroDivisors
      exact inferInstanceAs (IsReduced (Spec (X.residueField i.1)))
  haveI : IsReduced (genericPointSpectrumCoproduct X) :=
    IsReduced.of_openCover _
      (sigmaOpenCover (fun η : genericPoints X ↦ Spec (X.residueField η.1)))
  have hrel := Hom.bijOn_genericPoints_toNormalization_of_isNormal
    (genericPointSpectrumCoproductTo X) (genericPointSpectrumCoproduct_isNormal X)
  refine ⟨bijOn_genericPoints X, ?_⟩
  intro η hη
  obtain ⟨y, hy, rfl⟩ := hrel.surjOn hη
  obtain ⟨⟨i, p⟩, rfl⟩ :=
    (sigmaMk (fun ξ : genericPoints X ↦ Spec (X.residueField ξ.1))).surjective y
  rw [sigmaMk_mk] at hη ⊢
  let k := Limits.Sigma.ι (fun ξ : genericPoints X ↦ Spec (X.residueField ξ.1)) i ≫
    (genericPointSpectrumCoproductTo X).toNormalization
  change IsIso (X.normalizationTo.stalkMap (k p))
  have hk : k ≫ X.normalizationTo = X.fromSpecResidueField i.1 := by
    calc
      k ≫ X.normalizationTo =
          Limits.Sigma.ι (fun ξ : genericPoints X ↦ Spec (X.residueField ξ.1)) i ≫
            ((genericPointSpectrumCoproductTo X).toNormalization ≫
              (genericPointSpectrumCoproductTo X).fromNormalization) := Category.assoc _ _ _
      _ = Limits.Sigma.ι (fun ξ : genericPoints X ↦ Spec (X.residueField ξ.1)) i ≫
          genericPointSpectrumCoproductTo X :=
        congrArg (fun g : genericPointSpectrumCoproduct X ⟶ X ↦
          Limits.Sigma.ι (fun ξ : genericPoints X ↦ Spec (X.residueField ξ.1)) i ≫ g)
          (Hom.toNormalization_fromNormalization (genericPointSpectrumCoproductTo X))
      _ = X.fromSpecResidueField i.1 := genericPointSpectrumCoproductTo_ι X i
  have hsource : IsField (X.normalization.presheaf.stalk (k p)) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ (k p) hη
  have htarget : IsField (X.presheaf.stalk (X.normalizationTo (k p))) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ _
      ((bijOn_genericPoints X).mapsTo hη)
  letI := hsource.toField
  letI := htarget.toField
  have hsurj : Function.Surjective ((k ≫ X.normalizationTo).stalkMap p) := by
    rw [hk]
    exact (X.fromSpecResidueField i.1).stalkMap_surjective p
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(X.normalizationTo.stalkMap (k p)).hom.injective, ?_⟩
  intro b
  obtain ⟨a, ha⟩ := hsurj ((k.stalkMap p) b)
  refine ⟨a, (k.stalkMap p).hom.injective ?_⟩
  rw [Hom.stalkMap_comp] at ha
  exact ha

attribute [instance] isBirational_of_isReduced_finiteComponents

/-- An integral morphism that is birational on quasi-compact opens receives the normalization
morphism of its target. The intermediate scheme has finite irreducible components on quasi-compact
opens, and the resulting map identifies the source normalization with its normalization. The
finite-component conclusion is bound as an instance only inside the remaining conclusion so that
the intermediate normalization and its canonical morphism are available there. -/
@[stacks 035Q]
theorem exists_factorization
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {X' : Scheme.{u}} (α : X' ⟶ X) [IsIntegralHom α]
    (hα : α.IsBirationalOnCompactOpens) :
    ∃ hX' : HasFiniteIrreducibleComponentsOnCompactOpens X',
      -- Local instance justification (proof-local temporary data): the existentially returned finite-component proof is installed only to form the intermediate normalization in this dependent conclusion.
      letI : HasFiniteIrreducibleComponentsOnCompactOpens X' := hX'
      ∃ β : X.normalization ⟶ X',
        β ≫ α = X.normalizationTo ∧
          ∃ e : X.normalization ≅ X'.normalization,
            β = e.hom ≫ X'.normalizationTo := sorry

/-- A morphism from a normal scheme that maps every generic point to a generic point factors
uniquely through the normalization morphism of a scheme with finitely many irreducible components
on quasi-compact opens. -/
@[stacks 035Q]
theorem existsUnique_lift_of_isNormal
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {Z : Scheme.{u}} (g : Z ⟶ X) (hZ : Z.isNormal)
    (hcomponents : Set.MapsTo g (genericPoints Z) (genericPoints X)) :
    ∃! h : Z ⟶ X.normalization, h ≫ X.normalizationTo = g := sorry

end Normalization

end AlgebraicGeometry.Scheme
