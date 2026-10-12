/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reflexive and torsion-free module sheaves

This file relates reflexivity, torsion-freeness, and the canonical morphism to the double dual
for coherent module sheaves on integral locally Noetherian schemes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The canonical morphism from a coherent module sheaf to its double dual is a monomorphism
exactly when the module sheaf is torsion-free. -/
@[stacks 0AY2]
theorem mono_toReflexiveHull_iff_isTorsionFree
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    Mono (toReflexiveHull ℱ) ↔ IsTorsionFree ℱ := sorry

namespace IsReflexive

/-- A coherent reflexive module sheaf on an integral locally Noetherian scheme is
torsion-free. -/
@[stacks 0AY2]
instance to_isTorsionFree
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ] :
    IsTorsionFree ℱ :=
  (mono_toReflexiveHull_iff_isTorsionFree ℱ).mp inferInstance

end IsReflexive

end AlgebraicGeometry.Scheme.Modules
