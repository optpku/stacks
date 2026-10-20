/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.PowerSlice
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/- Lemma 51.22.7. Let `d = d(Gr_I(A))` and `q₀ = q(Gr_I(A))`. If `c ≤ n`,
`n ≥ max (q₀ + (1 + d) * c) ((2 + d) * c)`, and `K` is a finite-cohomology
derived `A / I ^ n`-module concentrated in degrees `-1` and `0` whose
degree-one Ext on finite modules is annihilated by the image of `I ^ c`, then
the Ext-one map induced by
`I ^ n / I ^ (2 * n) ⟶ I ^ (n - (1 + d) * c) / I ^ (2 * (n - (1 + d) * c))`
is zero.

The annihilation condition is stated over `A / I ^ n`, with the image of
`I ^ c`, as in the proof: arbitrary `A / I ^ n`-modules do not canonically
carry an `A / I ^ c`-module structure. -/
@[stacks 0GAD] #check (AlgebraicGeometry.IsBlowup.powerSliceExtOneMap_eq_zero :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) (hcn : c ≤ n)
    (hn : max
      (associatedGradedUniformityThreshold I +
        (1 + associatedGradedFiberDimension I) * c)
      ((2 + associatedGradedFiberDimension I) * c) ≤ n)
    (K : DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n)))
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    [Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I ^ n)) (-1)).obj K)]
    [Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat (A ⧸ I ^ n)) 0).obj K)]
    (hExt : twoTermExtOneAnnihilatedByIdealOnFiniteModules K
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c))),
    (DerivedCategory.Ext.moduleFunctor K (1 : ℤ)).map
      (Ideal.PowerSlice.diagonalTransition I n
        (n - (1 + associatedGradedFiberDimension I) * c)
        (Nat.sub_le n ((1 + associatedGradedFiberDimension I) * c))) = 0)

end AlgebraicGeometry.IsBlowup
