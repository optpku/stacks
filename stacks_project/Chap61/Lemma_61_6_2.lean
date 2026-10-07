module

public import ReasLib.RingTheory.RingHom.IndZariski.ConnectedComponents
import StacksCheckRecall

/-!
# Lemma 61.6.2

An ind-Zariski algebra realizing a prescribed profinite map into the
connected-components quotient of a spectrum.
-/

@[expose] public section

universe u v

open PrimeSpectrum

/- Lemma 61.6.2: `hcomm` descends to compatibility over
`ConnectedComponents (PrimeSpectrum A)`, and the homeomorphism induced by `p`
transports the pullback square to the component square. -/
@[stacks 097D]
#check
  (RingHom.IndZariski.exists_pullback_of_continuousMap_connectedComponents :
    ∀ {A : Type u} [CommRing A] {T : Type v}
      [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T],
      (φ : C(T, ConnectedComponents (PrimeSpectrum A))) →
        ∃ (B : Type (max u v)) (_ : CommRing B) (f : A →+* B)
          (p : C(PrimeSpectrum B, T))
          (hcomm : ∀ y, ConnectedComponents.mk (PrimeSpectrum.comap f y) = φ (p y)),
          f.IndZariski ∧
            IsHomeomorph (ConnectedComponents.pullback.comparison hcomm) ∧
            IsHomeomorph p.continuous.connectedComponentsLift)
