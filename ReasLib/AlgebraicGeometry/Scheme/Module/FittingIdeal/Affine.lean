/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal

/-!
# Fitting ideal sheaves on affine schemes

This file identifies the Fitting ideal sheaf of an associated module sheaf with the
ideal-sheaf datum induced by the corresponding module Fitting ideal.
-/

@[expose] public section

open AlgebraicGeometry
open scoped FittingIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The Fitting ideal sheaf of an associated module sheaf is the ideal-sheaf datum induced by
the corresponding Fitting ideal of the module. -/
theorem fittingIdealSheaf_tilde
    {R : Type u} [CommRing R] (M : ModuleCat (CommRingCat.of R)) [Module.Finite R M]
    (i : ℕ) :
    fittingIdealSheaf (tilde M) i =
      idealSheafDataOfIdealOnSpec (Fit[R]_(i)(M)) := sorry

end AlgebraicGeometry.Scheme
