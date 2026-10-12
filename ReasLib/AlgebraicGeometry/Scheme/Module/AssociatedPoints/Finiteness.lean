/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Finiteness of associated points

This file records the finiteness of the associated points of a coherent scheme module on a
quasi-compact open subset.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- The associated points of a coherent module that lie in a quasi-compact open subset form a
finite set. -/
@[stacks 05AF]
theorem associatedPoints_inter_quasiCompactOpen_finite
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    (associatedPoints ℱ ∩ (U : Set X)).Finite := sorry

end AlgebraicGeometry.Scheme.Modules
