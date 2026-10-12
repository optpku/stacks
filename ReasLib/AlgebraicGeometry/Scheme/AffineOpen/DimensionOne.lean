/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsAffine X]
  [∀ x : X, IsNoetherianRing (X.presheaf.stalk x)]

/-- A quasi-compact open of an affine scheme is affine if every stalk ring is Noetherian and has
Krull dimension at most one. -/
theorem isAffineOpen_of_quasiCompact_of_stalk_ringKrullDim_le_one
    (hDim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)
    (U : X.Opens) [QuasiCompact U.ι] :
    IsAffineOpen U := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]

/-- A finite set of points with Noetherian stalks of Krull dimension at most one in an integral
separated scheme is contained in an affine open. -/
theorem exists_affineOpen_containing_finiteSet_of_stalkNoetherianDimLEOne
    (S : Set X) (hS : S.Finite)
    (hNoeth : ∀ x : X, x ∈ S → IsNoetherianRing (X.presheaf.stalk x))
    (hDim : ∀ x : X, x ∈ S → ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    ∃ U : X.affineOpens, S ⊆ ((U : X.Opens) : Set X) := sorry

end AlgebraicGeometry.Scheme
