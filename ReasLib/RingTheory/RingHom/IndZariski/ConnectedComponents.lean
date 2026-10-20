/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski
public import ReasLib.Topology.ConnectedComponents.Pullback
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

open PrimeSpectrum

namespace RingHom.IndZariski

/-- A closed subset of the connected-components space of a commutative-ring
spectrum is realized by a surjective ind-Zariski ring homomorphism whose
spectral image is the inverse image of that subset. -/
@[stacks 097C]
theorem exists_surjective_of_isClosed_connectedComponents
    {A : Type u} [CommRing A] {T : Set (ConnectedComponents (PrimeSpectrum A))}
    (hT : IsClosed T) :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      Function.Surjective f ∧ f.IndZariski ∧
        Set.range (comap f) = ConnectedComponents.mk ⁻¹' T :=
  sorry

/-- A closed subset of the connected-components space of a commutative-ring
spectrum has inverse image equal to the zero locus of an ideal whose quotient
map is ind-Zariski. -/
theorem exists_quotientMk_of_isClosed_connectedComponents
    {A : Type u} [CommRing A] {T : Set (ConnectedComponents (PrimeSpectrum A))}
    (hT : IsClosed T) :
    ∃ I : Ideal A,
      (Ideal.Quotient.mk I).IndZariski ∧
        zeroLocus (I : Set A) = ConnectedComponents.mk ⁻¹' T :=
  sorry

/-- A continuous map from a profinite space into the connected-components space
of a spectrum is realized by an ind-Zariski map whose pullback comparison and
connected-components lift are homeomorphisms. -/
@[stacks 097D]
theorem exists_pullback_of_continuousMap_connectedComponents
    {A : Type u} [CommRing A] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (φ : C(T, ConnectedComponents (PrimeSpectrum A))) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (f : A →+* B)
      (p : C(PrimeSpectrum B, T))
      (hcomm : ∀ y, ConnectedComponents.mk (comap f y) = φ (p y)),
      f.IndZariski ∧
        IsHomeomorph (ConnectedComponents.pullback.comparison hcomm) ∧
        IsHomeomorph p.continuous.connectedComponentsLift :=
  sorry

end RingHom.IndZariski
