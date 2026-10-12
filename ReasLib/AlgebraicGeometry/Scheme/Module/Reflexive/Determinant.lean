/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Regular

/-!
# Reflexive determinants

This file defines the reflexive determinant of a coherent module and records its
invertibility on a regular scheme of dimension at most two when the module has
constant rank on a nonempty open subscheme.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant

variable {X : Scheme.{u}}

/-- The reflexive determinant of rank `r` of a module sheaf is the double dual of its
`r`-th exterior power. -/
noncomputable abbrev sheaf (r : ℕ) (ℱ : X.Modules) : X.Modules :=
  reflexiveHull (Λ[r] ℱ)

/-- The reflexive determinant of a coherent module that has rank `r` on a nonempty open
subscheme of a regular integral scheme of dimension at most two is invertible. -/
theorem isInvertible_of_nonempty_open_isFiniteLocallyFreeOfRank
    [IsIntegral X] [Scheme.Regular X]
    (r : ℕ) (ℱ : X.Modules) [ℱ.IsCoherent]
    (hdim : topologicalKrullDim X ≤ 2)
    (U : X.Opens) (hU : Set.Nonempty (U : Set X))
    [SheafOfModules.IsFiniteLocallyFreeOfRank r (ℱ.over U)] :
    Scheme.Modules.Invertible (sheaf r ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.ReflexiveDeterminant
