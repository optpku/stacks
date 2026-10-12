/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Quasi-affine schemes and quasi-compact immersions

A quasi-compact immersion into a quasi-affine scheme has quasi-affine source.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

/-- Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine. -/
theorem of_isImmersion_of_quasiCompact
    {X X' : Scheme.{u}} {i : X' ⟶ X} (hX : X.IsQuasiAffine)
    (hi : IsImmersion i) (hqc : QuasiCompact i) :
    X'.IsQuasiAffine := by
  exact @Scheme.IsQuasiAffine.of_isImmersion _ _ i hX hi
    (@QuasiCompact.compactSpace_of_compactSpace _ _ i hqc hX.toCompactSpace)

end AlgebraicGeometry.Scheme.IsQuasiAffine
