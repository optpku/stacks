/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType

@[expose] public section

/-!
# Retrocompact subsets of schemes

This file characterizes retrocompact subsets of schemes using affine open subsets.
-/

open Topology

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {E : Set X}

/-- A subset of a scheme is retrocompact if and only if its intersection with every affine open
subset is compact. -/
theorem isRetrocompact_iff_forall_isAffineOpen :
    IsRetrocompact E ↔ ∀ U : X.Opens, IsAffineOpen U → IsCompact (E ∩ U) := sorry

/-- On a quasi-separated scheme, an open subset is retrocompact exactly when it is a finite
union of affine opens. -/
theorem isRetrocompact_iff_exists_finite_affineOpen_cover
    [QuasiSeparatedSpace X] (U : X.Opens) :
    IsRetrocompact (U : Set X) ↔
      ∃ s : Set X.affineOpens, s.Finite ∧
        U = ⨆ V ∈ s, (V : X.Opens) := sorry

/-- On a quasi-compact quasi-separated scheme, an open subset is retrocompact exactly when its
closed complement supports finite-type ideal-sheaf data. -/
theorem isRetrocompact_iff_exists_finiteTypeIdealSheaf_support_eq_compl
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens) :
    IsRetrocompact (U : Set X) ↔
      ∃ I : X.IdealSheafData, I.IsFiniteType ∧ I.support = U.compl := sorry

/-- For an open subset of a quasi-compact quasi-separated scheme, retrocompactness, compactness,
finite affine-open coverability, and support-complement presentation by finite-type ideal-sheaf
data are equivalent. -/
theorem retrocompactOpen_tfae [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens) :
    List.TFAE [
      IsRetrocompact (U : Set X),
      IsCompact (U : Set X),
      ∃ s : Set X.affineOpens, s.Finite ∧ U = ⨆ V ∈ s, (V : X.Opens),
      ∃ I : X.IdealSheafData, I.IsFiniteType ∧ I.support = U.compl
    ] := sorry

end AlgebraicGeometry.Scheme
