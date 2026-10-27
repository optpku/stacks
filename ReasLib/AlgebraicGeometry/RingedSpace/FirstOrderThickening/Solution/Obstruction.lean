/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Fiber
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# A conditional Ext² obstruction to first-order ringed-space solutions
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Solution

variable {S S' X : RingedSpace.{u}}
variable (t : S ⟶ S') [IsFirstOrderThickening t]
variable (f : X ⟶ S) (G : X.Modules)
variable (c : Hom.idealModule t ⟶ (f _*).obj G)

/-- If the canonical naive-cotangent comparison maps extend to a distinguished triangle,
then a first-order ringed-space solution with prescribed kernel map exists exactly when
the connecting Ext² image of the coefficient-pulled tautological extension class vanishes. -/
theorem exists_iff_connecting_eq_zero
    (gamma :
      (DerivedCategory.Q (C := X.Modules)).obj NL[f] ⟶
        ((modulePullbackDerived f).obj
          ((DerivedCategory.Q (C := S.Modules)).obj NL[t]))⟦(1 : ℤ)⟧)
    (hDelta :
      Triangle.mk (naiveCotangentComparison t f)
        ((DerivedCategory.Q (C := X.Modules)).map (NaiveCotangent.comparison f t)) gamma ∈
          distTriang (DerivedCategory X.Modules)) :
    Nonempty (IsoClass t f G c) ↔
      ShiftedHom.comp gamma
        (extOne_map (cPull t f c) (selfExtensionClass t))
        (rfl : (1 : ℤ) + 1 = 2) = 0 := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Solution
