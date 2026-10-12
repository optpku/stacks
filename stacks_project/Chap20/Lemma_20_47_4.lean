/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Triangulated
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.4: fixed-degree pseudo-coherence satisfies the shifted two-out-of-three
property for distinguished triangles.  The reusable statements live in the ringed-space
facade, backed by the bundled ringed-site owner. -/

@[stacks 08CD "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.obj₃

@[stacks 08CD "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.obj₂

@[stacks 08CD "(3)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.obj₁

-- Shift transport and the canonical fixed-bound object property are the reusable glue.
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.shift_iff
#check @RingedSite.Hom.ModuleDerived.mPseudoCoherent_isTriangulatedClosed₂

