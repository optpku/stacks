/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein.Regular
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 48.24.3: A regular scheme is Gorenstein. -/
@[stacks 0DWG] #check
  (AlgebraicGeometry.Scheme.instGorensteinOfRegular :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.Scheme.Regular X],
      AlgebraicGeometry.Scheme.Gorenstein X)
