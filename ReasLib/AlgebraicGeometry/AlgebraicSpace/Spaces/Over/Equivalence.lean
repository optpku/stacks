/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Over.BaseChange

/-!
# Equivalences classifying algebraic spaces over an algebraic space

Base change identifies finite-type algebraic spaces over an algebraic space
with based functors from its associated groupoid fibration to the primed
finite-type fibration. The same holds for finite-presentation, flat, proper
algebraic spaces and the corresponding primed fibration.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- Base change from finite-type algebraic spaces over `T` to based functors
from its associated groupoid fibration to the primed finite-type fibration is
an equivalence of categories. -/
instance FtOver.yoneda.instIsEquivalence {S : Scheme.{u}} (T : AlgebraicSpace S) :
    (FtOver.yoneda T).IsEquivalence := sorry

/-- Base change from finite-presentation, flat, proper algebraic spaces over
`T` to based functors from its associated groupoid fibration to the corresponding
primed fibration is an equivalence of categories. -/
instance FpFlatProperOver.yoneda.instIsEquivalence {S : Scheme.{u}}
    (T : AlgebraicSpace S) : (FpFlatProperOver.yoneda T).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces
