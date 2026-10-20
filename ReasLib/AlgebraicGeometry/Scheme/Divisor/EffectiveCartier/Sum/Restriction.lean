/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum

/-!
# Restriction sequences for sums of effective Cartier divisors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- If an effective Cartier divisor `D'` is the sum of an effective Cartier divisor `D` and
an effective Cartier divisor `C`, with `D ⊆ D'`, then the restriction of the negative sheaf
of `D` to `C`, the structure sheaf of `D'`, and the structure sheaf of `D` form a short exact
sequence after pushforward to the ambient scheme. -/
theorem exists_negSheaf_restriction_shortExact_of_eq_sum
    (D D' C : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor D'.subschemeι]
    [IsEffectiveCartierDivisor C.subschemeι]
    (hsubset : D' ≤ D) (hsum : D' = effectiveCartierDivisorSum D C) :
    ∃ (f :
        (Scheme.Modules.pushforward C.subschemeι).obj
            ((Scheme.Modules.pullback C.subschemeι).obj D.negSheaf) ⟶
          (Scheme.Modules.pushforward D'.subschemeι).obj
            (SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules))
      (g :
        (Scheme.Modules.pushforward D'.subschemeι).obj
            (SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules) ⟶
          (Scheme.Modules.pushforward D.subschemeι).obj
            (SheafOfModules.unit D.subscheme.ringCatSheaf : D.subscheme.Modules))
      (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
