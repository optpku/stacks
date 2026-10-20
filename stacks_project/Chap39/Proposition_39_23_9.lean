/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.InvariantSpectrum.Quotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Proposition 39.23.9 (1): the map from the affine object scheme to the spectrum of
the invariant equalizer ring is finite locally free. -/
@[stacks 03BM] #check
  (AlgebraicGeometry.GroupoidScheme.invariantSpectrumMap_isFiniteLocallyFree :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
      (eU : Spec (CommRingCat.of A) ≅ G.U.left)
      (eR : Spec (CommRingCat.of B) ≅ G.R.left)
      (h_source : eR.hom ≫ G.s.left =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
      (h_target : eR.hom ≫ G.t.left =
        Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
      [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
      [IsEquivalenceRelation G.t G.s],
      IsFiniteLocallyFree (invariantSpectrumMap G tSharp eU))

/- Proposition 39.23.9 (2): the arrow scheme is canonically the kernel pair of the map to
the invariant spectrum. -/
@[stacks 03BM] #check
  (AlgebraicGeometry.GroupoidScheme.invariantKernelPairComparison_isIso :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
      (eU : Spec (CommRingCat.of A) ≅ G.U.left)
      (eR : Spec (CommRingCat.of B) ≅ G.R.left)
      (h_source : eR.hom ≫ G.s.left =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
      (h_target : eR.hom ≫ G.t.left =
        Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
      [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
      [IsEquivalenceRelation G.t G.s],
      IsIso (G.toPreRelation.kernelPairLift
        (invariantSpectrumQuotientMap G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))
        (invariantSpectrumQuotientMap_equalizes G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))))

/- Proposition 39.23.9 (3): the invariant spectrum represents the quotient sheaf in the
fppf topology over the original base scheme. -/
@[stacks 03BM] #check
  (AlgebraicGeometry.GroupoidScheme.invariantQuotientComparison_fppf_isIso :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (tSharp : A →+* B)
      (eU : Spec (CommRingCat.of A) ≅ G.U.left)
      (eR : Spec (CommRingCat.of B) ≅ G.R.left)
      (h_source : eR.hom ≫ G.s.left =
        Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
      (h_target : eR.hom ≫ G.t.left =
        Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
      [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
      [IsEquivalenceRelation G.t G.s],
      IsIso (@Scheme.PreRelation.quotientSheafDesc _ _ _ G.toPreRelation
        (StandardTopology.fppf.overTopology S)
        (StandardTopology.overTopologySubcanonical StandardTopology.fppf S)
        (invariantSpectrumQuotientMap G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))
        (invariantSpectrumQuotientMap_equalizes G tSharp eU
          (invariantSpectrumMap_effectiveEpi G tSharp eU eR h_source h_target)
          (invariantSpectrumMap_respectsBase G tSharp eU eR h_source h_target))))

end AlgebraicGeometry.GroupoidScheme
