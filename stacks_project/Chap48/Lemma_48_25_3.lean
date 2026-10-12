/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap48.Definition_48_25_2_Gorenstein
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 48.25.3: a scheme morphism with locally Noetherian fibres is Gorenstein if and
only if it is flat and all its fibres are Gorenstein schemes. -/
@[stacks 0C05] #check
  (AlgebraicGeometry.gorenstein_iff_flat_and_fibers :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [∀ y : Y, AlgebraicGeometry.IsLocallyNoetherian (f.fiber y)],
      AlgebraicGeometry.Gorenstein f ↔
        AlgebraicGeometry.Flat f ∧
          ∀ y : Y, AlgebraicGeometry.Scheme.Gorenstein (f.fiber y))
