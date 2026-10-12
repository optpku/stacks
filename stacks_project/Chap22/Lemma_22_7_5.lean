/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Replacement
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}
variable {n : ℕ}
variable (S : ComposableArrows (DifferentialGradedModule.{u, w} A) n)

/- Lemma 22.7.5 (09JX): every finite composable row of DG-modules has a comparison row
whose arrows are admissibly monic and whose comparison components are homotopy equivalences. -/
@[stacks 09JX] #check
  (HomotopyReplacement.exists_admissibleMono S :
    ∃ (T : ComposableArrows (DifferentialGradedModule.{u, w} A) n) (phi : T ⟶ S),
      ComposableArrows.arrowProperty (admissibleMonomorphisms A) T ∧
        ComposableArrows.componentProperty (homotopyEquivalences A) phi)

/- The pointwise companion exposes the conditions at the canonical `Fin` indices. -/
#check (HomotopyReplacement.exists_admissibleMono_pointwise S :
  ∃ (T : ComposableArrows (DifferentialGradedModule.{u, w} A) n) (phi : T ⟶ S),
    (∀ i : Fin n, IsAdmissibleMono (T.map' i.1 (i.1 + 1))) ∧
      ∀ i : Fin (n + 1), homotopyEquivalences A (phi.app i))
