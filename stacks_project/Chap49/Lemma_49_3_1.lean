/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Discriminant
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 49.3.1: a finite locally free morphism of schemes is étale if and only if its
discriminant locus is empty. -/
@[stacks 0BJF] #check
  (AlgebraicGeometry.Scheme.Hom.etale_iff_discriminantLocus_eq_empty :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFiniteLocallyFree f],
      Etale f ↔ f.discriminantLocus = ∅)
