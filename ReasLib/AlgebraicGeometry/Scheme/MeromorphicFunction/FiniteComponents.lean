/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Affine
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic
public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak.ZeroDivisor
public import ReasLib.Topology.Presheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Meromorphic functions on schemes with locally finite components

The meromorphic-function sheaf of a scheme whose quasi-compact opens have finitely many
irreducible components can be described using the stalks at the generic points of those
components. This file also records the resulting quasi-coherence and total-quotient properties.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The canonical morphism from the spectrum of the local ring at a generic point to the
scheme. -/
abbrev genericPointStalkMap (η : genericPoints X) :
    Spec (CommRingCat.of (X.presheaf.stalk η.1)) ⟶ X :=
  X.fromSpecStalk η.1

/-- The direct image on `X` of the structure sheaf of the spectrum of the local ring at a
generic point. -/
abbrev genericPointStalkPushforwardSheaf (η : genericPoints X) :
    TopCat.Sheaf CommRingCat X.toTopCat :=
  (TopCat.Sheaf.pushforward CommRingCat (genericPointStalkMap X η).base).obj
    (Spec (CommRingCat.of (X.presheaf.stalk η.1))).sheaf

/-- The product of the direct images of the generic-point local-ring structure sheaves. -/
abbrev genericPointStalkPushforwardProductSheaf :
    TopCat.Sheaf CommRingCat X.toTopCat :=
  ∏ᶜ fun η : genericPoints X ↦ genericPointStalkPushforwardSheaf X η

/-- Under finite-component and weak-association hypotheses, the meromorphic-function sheaf is
isomorphic to the product of the direct images of its generic-point local rings. -/
theorem meromorphicFunctionSheaf_iso_genericPointStalkPushforwardProduct
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X) :
    IsIsomorphic X.toLocallyRingedSpace.meromorphicFunctionSheaf
      (genericPointStalkPushforwardProductSheaf X) := sorry

/-- Under finite-component and weak-association hypotheses, the meromorphic-function algebra is
quasi-coherent as a module over the structure sheaf. -/
theorem meromorphicFunctionSheaf_isQuasicoherent
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X) :
    ((restrictionAlong X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom).obj
      (SheafOfModules.unit
        (ringSheaf (Opens.grothendieckTopology X.toTopCat)
          X.toLocallyRingedSpace.meromorphicFunctionSheaf) :
        ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
          X.toLocallyRingedSpace.meromorphicFunctionSheaf)).IsQuasicoherent := sorry

namespace Scheme

/-- The sheaf of meromorphic functions, bundled as a quasi-coherent algebra over the structure
sheaf. -/
noncomputable def meromorphicFunctionQcAlgebra
    (X : Scheme.{u}) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X) : X.QcAlgebraUnder :=
  ⟨Under.mk X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom,
    meromorphicFunctionSheaf_isQuasicoherent X hweak⟩

end Scheme

/-- The submonoid of the local ring at `x` consisting of germs represented locally by
meromorphic-function denominators. -/
noncomputable def meromorphicDenominatorStalk (X : Scheme.{u}) (x : X) :
    Submonoid (X.presheaf.stalk x) :=
  ⨆ (U : X.Opens) (hx : x ∈ U),
    Submonoid.map (X.presheaf.germ U x hx).hom
      ((X.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op U))

/-- If the weakly associated points are generic points of irreducible components and
quasi-compact opens have finitely many irreducible components, the local meromorphic
denominators are exactly the non-zero-divisors. -/
theorem meromorphicDenominatorStalk_eq_nonZeroDivisors
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X) (x : X) :
    meromorphicDenominatorStalk X x = nonZeroDivisors (X.presheaf.stalk x) := by
  classical
  -- Local instance justification (proof-local temporary data): the affine structure sheaf
  -- module is transported to the unit module for the quasi-coherence argument.
  letI : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Limits.coproductUniqueIso
        (fun _ : PUnit ↦ SheafOfModules.unit X.ringCatSheaf))
      (inferInstanceAs
        ((SheafOfModules.free (R := X.ringCatSheaf) PUnit).IsQuasicoherent))
  have weaklyAssociatedPrimes_subset_minimalPrimes
      (U : X.Opens) (hU : IsAffineOpen U) :
      weaklyAssociatedPrimes Γ(X, U) Γ(X, U) ⊆ minimalPrimes Γ(X, U) := by
    intro q hq
    let p : PrimeSpectrum Γ(X, U) := ⟨q, (Classical.choose_spec hq).1.1⟩
    have hpweak : hU.fromSpec p ∈ X.weakAss :=
      (Scheme.Modules.mem_weaklyAssociatedPrimes_sections_iff_fromSpec_mem_weakAss
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) hU p).mp hq
    have hpgeneric : hU.fromSpec p ∈ genericPoints X := hweak hpweak
    have hopen : Topology.IsOpenEmbedding (hU.fromSpec : Spec Γ(X, U) ⟶ X) :=
      (inferInstance : IsOpenImmersion hU.fromSpec).base_open
    have hmeet :
        (closure ({hU.fromSpec p} : Set X) ∩ Set.range hU.fromSpec).Nonempty :=
      ⟨hU.fromSpec p, subset_closure (Set.mem_singleton _), p, rfl⟩
    have hcomponent :
        hU.fromSpec ⁻¹' closure ({hU.fromSpec p} : Set X) ∈
          irreducibleComponents (Spec Γ(X, U)) :=
      preimage_mem_irreducibleComponents hpgeneric hopen hmeet
    have hclosure :
        closure ({p} : Set (Spec Γ(X, U))) =
          hU.fromSpec ⁻¹' closure ({hU.fromSpec p} : Set X) := by
      rw [hopen.isOpenMap.preimage_closure_eq_closure_preimage hopen.continuous]
      congr 1
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hopen.injective.eq_iff.symm
    have hpminimal : p.asIdeal ∈ minimalPrimes Γ(X, U) := by
      rw [← PrimeSpectrum.vanishingIdeal_singleton]
      exact PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr
        (by exact hclosure.symm ▸ hcomponent)
    exact hpminimal
  apply le_antisymm
  · refine iSup_le fun U ↦ iSup_le fun hxU ↦ ?_
    rintro z ⟨s, hs, rfl⟩
    change s ∈ ⨅ y : U, Submonoid.comap
      (X.presheaf.germ U y.1 y.2).hom
        (nonZeroDivisors (X.presheaf.stalk y.1)) at hs
    exact Submonoid.mem_iInf.mp hs ⟨x, hxU⟩
  · intro z hz
    obtain ⟨W, hxW, t, rfl⟩ := X.presheaf.exists_germ_eq z
    obtain ⟨U, hU, hxU, hUW⟩ :=
      exists_isAffineOpen_mem_and_subset (U := W) (x := x) hxW
    let s : Γ(X, U) := X.presheaf.map (homOfLE hUW).op t
    have hsGerm : X.presheaf.germ U x hxU s = X.presheaf.germ W x hxW t := by
      exact X.presheaf.germ_res_apply (homOfLE hUW) x hxU t
    rw [← hsGerm] at hz ⊢
    let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
    -- Local instance justification (proof-local temporary data): this is the selected
    -- affine-open stalk algebra used to compare sections with the stalk at `x`.
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    -- Local instance justification (defeq pin): this is the localization structure at
    -- the prime ideal selected from the affine-open point `x`.
    letI : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
      hU.isLocalization_stalk ⟨x, hxU⟩
    have hbad (q : minimalPrimes Γ(X, U)) (hsq : s ∈ q.1) : ¬ q.1 ≤ p := by
      intro hqp
      have hdis : Disjoint (p.primeCompl : Set Γ(X, U)) (q.1 : Set Γ(X, U)) :=
        Set.disjoint_compl_left_iff_subset.mpr hqp
      have hqmap : q.1.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ∈
          minimalPrimes (X.presheaf.stalk x) := by
        have hqmap' : q.1.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) ∈
            ((⊥ : Ideal Γ(X, U)).map
              (algebraMap Γ(X, U) (X.presheaf.stalk x))).minimalPrimes := by
          rw [IsLocalization.minimalPrimes_map p.primeCompl]
          change Ideal.under Γ(X, U)
            (q.1.map (algebraMap Γ(X, U) (X.presheaf.stalk x))) ∈
              minimalPrimes Γ(X, U)
          rw [IsLocalization.under_map_of_isPrime_disjoint p.primeCompl
            (X.presheaf.stalk x) q.2.1.1 hdis]
          exact q.2
        simpa using hqmap'
      exact (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
        (Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk x)) hsq) hqmap) hz
    -- Local instance justification (proof-local temporary data): the finite indexing type
    -- of minimal primes is needed for the product used to choose a denominator.
    letI : Fintype (minimalPrimes Γ(X, U)) :=
      (Scheme.affineOpen_sections_finite_minimalPrimes ⟨U, hU⟩).fintype
    choose a haQ haP using fun q : {q : minimalPrimes Γ(X, U) // s ∈ q.1} ↦
      Set.not_subset.mp (hbad q.1 q.2)
    let f : Γ(X, U) := ∏ q : {q : minimalPrimes Γ(X, U) // s ∈ q.1}, a q
    have hfnot : f ∉ p := by
      intro hf
      change (∏ q : {q : minimalPrimes Γ(X, U) // s ∈ q.1}, a q) ∈ p at hf
      rw [Ideal.IsPrime.prod_mem_iff] at hf
      obtain ⟨q, -, hq⟩ := hf
      exact haP q hq
    let V : X.Opens := X.basicOpen f
    have hV : IsAffineOpen V := hU.basicOpen f
    have hxV : x ∈ V := by
      rw [Scheme.mem_basicOpen X f x hxU]
      change IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) f)
      exact IsLocalization.map_units (M := p.primeCompl)
        (S := X.presheaf.stalk x) ⟨f, hfnot⟩
    let sV : Γ(X, V) := X.presheaf.map (homOfLE (X.basicOpen_le f)).op s
    have hsV : sV ∈ nonZeroDivisors Γ(X, V) := by
      rw [mem_nonZeroDivisors_iff_right]
      intro b hsb
      by_contra hb
      have hsUnion : sV ∈ ⋃ q ∈ weaklyAssociatedPrimes Γ(X, V) Γ(X, V), q := by
        rw [weaklyAssociatedPrimes.biUnion_eq_zero_divisors]
        refine ⟨b, hb, ?_⟩
        change sV * b = 0
        rw [mul_comm]
        exact hsb
      simp only [Set.mem_iUnion] at hsUnion
      obtain ⟨q, hqweak, hsq⟩ := hsUnion
      have hqmin : q ∈ minimalPrimes Γ(X, V) :=
        weaklyAssociatedPrimes_subset_minimalPrimes V hV hqweak
      -- Local instance justification (defeq pin): the basic-open localization identifies
      -- sections on `V` with the localization of sections on the affine open `U`.
      letI : IsLocalization.Away f Γ(X, V) := hU.isLocalization_basicOpen f
      let qU : Ideal Γ(X, U) := Ideal.under Γ(X, U) q
      have hqUmin : qU ∈ minimalPrimes Γ(X, U) := by
        have hqmin' : q ∈ ((⊥ : Ideal Γ(X, U)).map
            (algebraMap Γ(X, U) Γ(X, V))).minimalPrimes := by simpa using hqmin
        rw [IsLocalization.minimalPrimes_map (Submonoid.powers f) Γ(X, V)] at hqmin'
        exact hqmin'
      have hsU : s ∈ qU := by
        rw [Ideal.mem_under]
        exact hsq
      have hfU : f ∉ qU := by
        have hd : Disjoint (Submonoid.powers f : Set Γ(X, U)) (qU : Set Γ(X, U)) :=
          (IsLocalization.disjoint_under_iff (Submonoid.powers f) Γ(X, V) q).mpr
            hqmin.isPrime.ne_top
        exact fun h ↦ Set.disjoint_left.mp hd (Submonoid.mem_powers f) h
      let qbad : {q : minimalPrimes Γ(X, U) // s ∈ q.1} := ⟨⟨qU, hqUmin⟩, hsU⟩
      apply hfU
      -- Local instance justification (proof-local temporary data): the prime ideal `qU`
      -- obtained in the contradiction argument is used for the prime-product criterion.
      letI : qU.IsPrime := hqUmin.isPrime
      change (∏ q : {q : minimalPrimes Γ(X, U) // s ∈ q.1}, a q) ∈ qU
      rw [Ideal.IsPrime.prod_mem_iff]
      exact ⟨qbad, Finset.mem_univ _, haQ qbad⟩
    have hle :
        Submonoid.map (X.presheaf.germ V x hxV).hom
            ((X.toLocallyRingedSpace.meromorphicFunctionDenominators).obj (op V)) ≤
          meromorphicDenominatorStalk X x :=
      le_iSup_of_le V (le_iSup_of_le hxV le_rfl)
    apply hle
    refine ⟨sV, ?_, ?_⟩
    · refine (LocallyRingedSpace.mem_meromorphicFunctionDenominators_iff
        (X := X.toLocallyRingedSpace) sV).2 ?_
      intro y
      -- Local instance justification (proof-local temporary data): this is the selected
      -- affine-open stalk algebra for the point `y`.
      letI : Algebra Γ(X, V) (X.presheaf.stalk y.1) :=
        TopCat.Presheaf.algebra_section_stalk X.presheaf y
      -- Local instance justification (defeq pin): this is the stalk localization at the
      -- prime ideal selected by the affine open `V` and point `y`.
      letI : IsLocalization.AtPrime (X.presheaf.stalk y.1)
          (hV.primeIdealOf y).asIdeal := hV.isLocalization_stalk y
      change algebraMap Γ(X, V) (X.presheaf.stalk y.1) sV ∈
        nonZeroDivisors (X.presheaf.stalk y.1)
      apply IsLocalization.map_nonZeroDivisors_le
        (R := Γ(X, V)) (S := X.presheaf.stalk y.1)
        (hV.primeIdealOf y).asIdeal.primeCompl
      exact ⟨sV, hsV, rfl⟩
    · exact X.presheaf.germ_res_apply (homOfLE (X.basicOpen_le f)) x hxV s

/-- At every point, the meromorphic-function stalk is a localization of the local ring at its
non-zero-divisors. -/
theorem meromorphicStalk_isLocalization
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X) (x : X) :
    IsLocalization (nonZeroDivisors (X.presheaf.stalk x))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk x) := by
  rw [← meromorphicDenominatorStalk_eq_nonZeroDivisors X hweak x]
  let T := X.toLocallyRingedSpace.meromorphicFunctionDenominators
  have hsub :
      TopCat.Presheaf.SectionLocalization.stalkSubmonoid
          (TopCat.Presheaf.SectionLocalization.ofTopCat T) x =
        meromorphicDenominatorStalk X x := by
    apply le_antisymm
    · rintro z ⟨U, hxU, s, rfl⟩
      have hle :
          Submonoid.map (X.presheaf.germ U x hxU).hom
              (X.toLocallyRingedSpace.meromorphicFunctionDenominators.obj (op U)) ≤
            meromorphicDenominatorStalk X x :=
        le_iSup_of_le U (le_iSup_of_le hxU le_rfl)
      exact hle ⟨s.1, s.2, rfl⟩
    · refine iSup_le fun U ↦ iSup_le fun hxU ↦ ?_
      rintro z ⟨s, hs, rfl⟩
      exact ⟨U, hxU, ⟨s, hs⟩, rfl⟩
  let unit := (TopCat.Presheaf.stalkFunctor CommRingCat x).map
    (CategoryTheory.toSheafify
      (Opens.grothendieckTopology X.toLocallyRingedSpace.toTopCat)
      T.localizationPresheaf)
  -- Local instance justification (defeq pin): the stalk-to-sheafification map is an
  -- isomorphism used to transport the localization structure to the meromorphic stalk.
  letI : IsIso unit := by
    dsimp only [unit]
    exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x CommRingCat T.localizationPresheaf
  let e := asIso unit
  let eAlg : ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj
        T.localizationPresheaf) ≃ₐ[X.presheaf.stalk x]
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk x :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun r ↦ by
        have hnat : T.toLocalizationPresheaf ≫
              CategoryTheory.toSheafify
                (Opens.grothendieckTopology X.toLocallyRingedSpace.toTopCat)
                T.localizationPresheaf =
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom := by
          have h := CategoryTheory.toSheafify_naturality
            (J := Opens.grothendieckTopology X.toLocallyRingedSpace.toTopCat)
            (η := X.toLocallyRingedSpace.presheaf.toTotalQuotientPresheaf)
          exact h.trans rfl
        change e.hom.hom
            (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
              T.toLocalizationPresheaf).hom r) =
          ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
            X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom).hom r
        simp only [e, asIso_hom, unit]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        exact congrArg
          (fun f ↦ ((TopCat.Presheaf.stalkFunctor CommRingCat x).map f).hom r) hnat }
  -- Local instance justification (defeq pin): the stalk of the section-localization
  -- presheaf carries its canonical localization structure for the final transport.
  letI : IsLocalization
      (TopCat.Presheaf.SectionLocalization.stalkSubmonoid
        (TopCat.Presheaf.SectionLocalization.ofTopCat T) x)
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj T.localizationPresheaf) :=
    TopCat.Presheaf.SectionLocalization.stalkIsLocalizationOfTopCat T x
  rw [← hsub]
  exact IsLocalization.isLocalization_of_algEquiv
    (TopCat.Presheaf.SectionLocalization.stalkSubmonoid
      (TopCat.Presheaf.SectionLocalization.ofTopCat T) x) eAlg

/-- On an affine open, meromorphic functions form the localization of regular functions at the
non-zero-divisors. -/
theorem meromorphicSections_isLocalization_of_isAffineOpen
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsLocalization (nonZeroDivisors Γ(X, U))
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.obj (op U)) := sorry

/-- Under finite-component and weak-association hypotheses, the rational-function ring is
isomorphic to the ring of global meromorphic functions. -/
theorem rationalFunctionRing_iso_meromorphicFunctions
    (X : Scheme.{u}) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ genericPoints X) :
    IsIsomorphic X.rationalFunctionRing X.toLocallyRingedSpace.meromorphicFunctions := sorry

end AlgebraicGeometry
