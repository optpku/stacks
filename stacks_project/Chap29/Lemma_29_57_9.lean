/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.LocallyQuasiFinite
import StacksCheckRecall

universe u

/- Lemma 29.57.9: A locally quasi-finite morphism with quasi-compact source has
universally bounded fibres. -/
@[stacks 03JA] #check
  (AlgebraicGeometry.LocallyQuasiFinite.universallyBoundedFibres :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.LocallyQuasiFinite f]
      [CompactSpace X],
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f)
