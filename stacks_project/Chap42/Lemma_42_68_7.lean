/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Theory.Characterization
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant.Theory

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Lemma 42.68.7: a determinant theory satisfying naturality, signed three-by-three
coherence, and compatibility with a chosen usual-determinant normalization on modules
annihilated by the maximal ideal is compatibly isomorphic to the canonical determinant
theory, extending that normalization. -/
@[stacks 02PB] #check (Module.FiniteLengthDeterminant.Theory.characterized :
  (D : Theory.{u, v} R) →
    D.IsNatural →
    D.IsCoherent →
    (e : D.restriction ≅ (canonical R).restriction) →
    D.AgreesOnResidue e →
    ∃ Φ : Iso D (canonical R), Φ.restrict = e)

end Module.FiniteLengthDeterminant.Theory
