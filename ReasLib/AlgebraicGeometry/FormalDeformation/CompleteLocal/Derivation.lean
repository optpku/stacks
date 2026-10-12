/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue

/-!
# Finite-dimensionality of residue derivations

Base-linear derivations from a Noetherian complete local algebra into its identified
residue field form a finite-dimensional vector space over that field.
-/

@[expose] public section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The base-linear derivations of a complete local algebra into its identified residue field
form a finite-dimensional vector space over the residue field. -/
instance finiteDimensional_derivation (S : CompleteLocalAlgCat Λ k) :
    FiniteDimensional k (Derivation Λ S.carrier k) := sorry

end CompleteLocalAlgCat
