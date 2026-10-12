/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.NegativeCohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry ENat

universe u

/- Lemma 33.48.2 (Enriques-Severi-Zariski): on a proper scheme over a field, the first
cohomology of a coherent module whose closed-point stalks have depth at least two vanishes after
every sufficiently negative twist by an ample invertible module. -/
@[stacks 0FD8] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.twistFirstCohomology_eventually_isZero :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (L F : X.Modules) [L.Invertible] [Scheme.Modules.IsAmple L] [F.IsCoherent],
      (∀ x : X, x ∈ closedPoints X →
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x)) →
        ∃ b : ℤ, ∀ d : ℤ, d ≤ b →
          IsZero (Scheme.Hom.cohomology f (F ⊗ L ^⊗ d) 1))
