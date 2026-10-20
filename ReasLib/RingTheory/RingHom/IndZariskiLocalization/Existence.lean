/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.RingHom.IndZariskiLocalization
public import ReasLib.RingTheory.RingHom.IndZariski.Retraction
public import ReasLib.Topology.ConnectedComponents.Pullback

@[expose] public section

/-!
# Existence of ind-(Zariski localization) ring homomorphisms

Filtered colimits of finite products of principal localizations realize closed
subsets and profinite base changes of connected-components spaces. They also
give faithfully flat refinements of ring maps identifying local rings and
faithfully flat extensions with the ind-Zariski retraction property.
-/

universe u v

open PrimeSpectrum

namespace RingHom.IndZariskiLocalization

/-- For a ring `A` and a closed subset `T` of its spectrum's connected-components
space, there exists a surjective ind-(Zariski localization) ring map whose
spectral image is the inverse image of `T`. -/
theorem exists_surjective_of_isClosed_connectedComponents
    {A : Type u} [CommRing A] {T : Set (ConnectedComponents (PrimeSpectrum A))}
    (hT : IsClosed T) :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      Function.Surjective f ∧ f.IndZariskiLocalization ∧
        Set.range (comap f) = ConnectedComponents.mk ⁻¹' T :=
  sorry

/-- A continuous map from a profinite space to the connected-components space
of a ring spectrum is realized by an ind-(Zariski localization), a cartesian
square of spaces, and a homeomorphism of connected-components spaces. -/
theorem exists_pullback_of_continuousMap_connectedComponents
    {A : Type u} [CommRing A] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (φ : C(T, ConnectedComponents (PrimeSpectrum A))) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (f : A →+* B)
      (p : C(PrimeSpectrum B, T))
      (hcomm : ∀ y, ConnectedComponents.mk (comap f y) = φ (p y)),
      f.IndZariskiLocalization ∧
        IsHomeomorph (ConnectedComponents.pullback.comparison hcomm) ∧
        IsHomeomorph p.continuous.connectedComponentsLift :=
  sorry

/-- A ring map identifying local rings admits a faithfully flat
ind-(Zariski localization) extension whose composite with the original map is
also an ind-(Zariski localization). -/
theorem exists_faithfullyFlat_of_isIsoOnLocalRings
    {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.IsIsoOnLocalRings) :
    ∃ (B' : Type u) (_ : CommRing B') (g : B →+* B'),
      g.FaithfullyFlat ∧ g.IndZariskiLocalization ∧
        (g.comp f).IndZariskiLocalization :=
  sorry

/-- Every commutative ring admits a faithfully flat ind-(Zariski localization)
extension to a ring for which every faithfully flat ind-Zariski map admits a
ring-homomorphism retraction. -/
theorem exists_faithfullyFlat_indZariskiRetraction (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      f.FaithfullyFlat ∧ f.IndZariskiLocalization ∧
        Algebra.HasFaithfullyFlatIndZariskiRetraction B :=
  sorry

end RingHom.IndZariskiLocalization
