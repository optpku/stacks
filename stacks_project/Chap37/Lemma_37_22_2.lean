/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.22.2: a scheme morphism with locally Noetherian fibres is Cohen--Macaulay
if and only if it is flat and all its fibres are Cohen--Macaulay schemes. -/
@[stacks 045S] #check
  (AlgebraicGeometry.cohenMacaulay_iff_flat_and_fibers :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [∀ y : Y, AlgebraicGeometry.IsLocallyNoetherian (f.fiber y)],
      AlgebraicGeometry.CohenMacaulay f ↔
        AlgebraicGeometry.Flat f ∧
          ∀ y : Y, AlgebraicGeometry.Scheme.CohenMacaulay (f.fiber y))
