/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree

/-!
# Pointwise finite-rank freeness

This module records when a module sheaf is free of a fixed finite rank on some open
neighbourhood of a specified point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

/-- A module sheaf is free of rank `r` at `x` if it has a rank-`r` free trivialization on an
open neighbourhood of `x`. -/
def IsFreeOfRankAt (r : ℕ) (F : X.Modules) (x : X) : Prop :=
  ∃ (U : Opens X) (_ : x ∈ U), Nonempty (F.over U ≅ SheafOfModules.freeFin r)

/-- Freeness of rank `r` at a point is characterized by a rank-`r` free trivialization on an
open neighbourhood of that point. -/
theorem isFreeOfRankAt_iff (r : ℕ) (F : X.Modules) (x : X) :
    IsFreeOfRankAt r F x ↔
      ∃ (U : Opens X) (_ : x ∈ U), Nonempty (F.over U ≅ SheafOfModules.freeFin r) := sorry

namespace IsFreeOfRankAt

/-- Pointwise freeness of fixed rank is invariant under isomorphism of module sheaves. -/
theorem iff_of_iso {F G : X.Modules} (e : F ≅ G) (r : ℕ) (x : X) :
    IsFreeOfRankAt r F x ↔ IsFreeOfRankAt r G x := sorry

end IsFreeOfRankAt

namespace IsFiniteLocallyFreeOfRank

/-- A finite locally free module sheaf of rank `r` is free of rank `r` at every point. -/
theorem isFreeOfRankAt (r : ℕ) (F : X.Modules) [IsFiniteLocallyFreeOfRank r F] (x : X) :
    IsFreeOfRankAt r F x := sorry

end IsFiniteLocallyFreeOfRank

end SheafOfModules
