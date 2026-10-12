/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.Lemma_82_4_4_Length

/-!
# Length of an 𝒪_X-module at a point

`hasLengthAt F x d` records that some étale scheme chart over `x` has Zariski-stalk
length `d`, matching the numeric payload of Definition 82.4.2 via `lengthOnEtaleChart`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- An `𝒪_X`-module `F` has length `d` at `x ∈ |X|` if some étale scheme chart over `x`
has Zariski-stalk length `d`. -/
def hasLengthAt (F : X.Modules) (x : Points X) (d : ℕ∞) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    Etale φ ∧ ∃ u : U.left,
      Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d

/-- `hasLengthAt F x d` unpacks as existence of an étale scheme chart over `x` with
Zariski-stalk length `d`. -/
theorem hasLengthAt_iff (F : X.Modules) (x : Points X) (d : ℕ∞) :
    hasLengthAt F x d ↔
      ∃ (U : Over S) (φ : ofOver U ⟶ X),
        Etale φ ∧ ∃ u : U.left,
          Points.mapOfOver φ u = x ∧ lengthOnEtaleChart φ F u = d :=
  sorry

/-- A given étale scheme chart with Zariski-stalk length `d` witnesses `hasLengthAt`. -/
theorem hasLengthAt_of_lengthOnEtaleChart {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    (F : X.Modules) {u : U.left} {x : Points X} {d : ℕ∞}
    (hu : Points.mapOfOver φ u = x) (hd : lengthOnEtaleChart φ F u = d) :
    hasLengthAt F x d :=
  sorry

/-- Finite nonzero length at a point is the existence of a strictly positive finite
length `d` at which `hasLengthAt` holds. -/
theorem hasFiniteNonzeroLengthAt_iff_hasLengthAt (F : X.Modules) (x : Points X) :
    hasFiniteNonzeroLengthAt F x ↔ ∃ d : ℕ∞, 0 < d ∧ d < ⊤ ∧ hasLengthAt F x d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
