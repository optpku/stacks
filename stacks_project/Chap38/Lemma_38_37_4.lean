/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 38.37.4: if `X` is quasi-compact and quasi-separated and `I` is a finite-type
quasi-coherent ideal sheaf on `X`, then the closed subscheme `I.subscheme` is the center of an
almost blowup square. -/
@[stacks 0EVA] #check
  (AlgebraicGeometry.exists_isAlmostBlowupSquare :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (I : X.IdealSheafData) [I.toModule.IsQuasicoherent], I.IsFiniteType →
        ∃ (X' : AlgebraicGeometry.Scheme.{u}) (b : X' ⟶ X),
          AlgebraicGeometry.IsAlmostBlowupSquare b I)
