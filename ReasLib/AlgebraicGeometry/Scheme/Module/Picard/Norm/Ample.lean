/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Existence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.FiniteSet
import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ample invertible modules and finite-morphism norms

This file owns descent of the existence of an ample invertible module along a finite morphism
admitting a norm.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- If a finite morphism admits a norm and its source has an ample invertible module, then its
target has an ample invertible module. -/
@[stacks 0BD0]
theorem hasAmpleInvertibleModule_target_of_finiteMorphismNorm
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] (d : ℕ)
    (hX : Scheme.Modules.HasAmpleInvertibleModule X)
    (hnorm : ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N) :
    Scheme.Modules.HasAmpleInvertibleModule Y := sorry

end AlgebraicGeometry.Scheme
