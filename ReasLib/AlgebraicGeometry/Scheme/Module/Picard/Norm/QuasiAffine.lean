/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Ample
import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Ample
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-affine schemes and finite-morphism norms

Quasi-affineness descends along finite morphisms admitting finite-morphism norms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

/-- If a finite morphism admits a norm and its source is quasi-affine, then its target is
quasi-affine. -/
@[stacks 0BD1]
theorem target_of_finiteMorphismNorm
    {X Y : Scheme} (π : X ⟶ Y) [IsFinite π] (d : ℕ)
    (hX : X.IsQuasiAffine)
    (hnorm : ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N) :
    Y.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
