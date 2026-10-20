/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.PerfectPairing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.SerrePairing
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.SerreFinrank
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh
open ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

section

variable {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
variable (h_dimension : topologicalKrullDim X.left ≤ 1)
variable [MonoidalCategory (RingedSpace.ModuleDerived X.left.toRingedSpace)]
  [BraidedCategory (RingedSpace.ModuleDerived X.left.toRingedSpace)]
  [MonoidalClosed (RingedSpace.ModuleDerived X.left.toRingedSpace)]
variable (e : fieldObject k ≅ ModuleCat.of k k)
variable (E : ObjectProperty.FullSubcategory
  (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.left.Modules))
variable (i : ℤ)

/- Remark 53.4.3 (1): for a finite locally free module `E` on a proper scheme `X`
of dimension at most one, the canonical pairing identifies the `k`-dual of
`H⁻ⁱ(X, E)` with `Hⁱ(X, Eᵛ ⊗ᴸ ω_X^•)`. -/
@[stacks 0BS4]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pairingWith_isPerfPair_of_perfect
      e X.hom ((VectorBundleK0.toPerfect X.left).obj E) i :
    LinearMap.IsPerfPair
      (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.perfectPairingWith
        e X.hom ((VectorBundleK0.toPerfect X.left).obj E) i))

end

section

variable {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
variable [Scheme.CohenMacaulay X.left] [EquidimensionalSpace X.left]
variable [MonoidalCategory (RingedSpace.ModuleDerived X.left.toRingedSpace)]
  [BraidedCategory (RingedSpace.ModuleDerived X.left.toRingedSpace)]
  [MonoidalClosed (RingedSpace.ModuleDerived X.left.toRingedSpace)]
variable (h_dimension : topologicalKrullDim X.left = 1)
variable (e : fieldObject k ≅ ModuleCat.of k k)
variable (E : ObjectProperty.FullSubcategory
  (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.left.Modules))
variable (i : ℤ)

/- Remark 53.4.3 (2): if moreover `X` is Cohen–Macaulay and equidimensional of
dimension one, the canonical pairing identifies the `k`-dual of `H⁻ⁱ(X, E)` with
`H¹⁺ⁱ(X, Eᵛ ⊗ ω_X)`. -/
@[stacks 0BS4]
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serrePairingWith_isPerfPair
      e X.hom 1 h_dimension E (1 + i) :
    LinearMap.IsPerfPair
      (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serrePairingWith
        e X.hom 1 h_dimension E (1 + i)))

end

section

variable {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
variable [Scheme.CohenMacaulay X.left] [EquidimensionalSpace X.left]
variable (h_dimension : topologicalKrullDim X.left = 1)
variable (L : X.left.Modules) [L.Invertible]

/- Remark 53.4.3 (3): for an invertible module `L` on a proper Cohen–Macaulay
equidimensional curve, `dim_k H⁰(X, L) = dim_k H¹(X, Lᵛ ⊗ ω_X)`. -/
@[stacks 0BS4]
#check
  (AlgebraicGeometry.Scheme.Hom.invertibleModule_h0_finrank_eq_dual_tensor_dualizing_h1
      X h_dimension L :
    Scheme.Hom.cohomologyFinrank X.hom L 0 =
      Scheme.Hom.cohomologyFinrank X.hom
        (Scheme.Modules.dual L ⊗ curveDualizingModule X.hom) 1)

/- Remark 53.4.3 (4): for an invertible module `L` on a proper Cohen–Macaulay
equidimensional curve, `dim_k H¹(X, L) = dim_k H⁰(X, Lᵛ ⊗ ω_X)`. -/
@[stacks 0BS4]
#check
  (AlgebraicGeometry.Scheme.Hom.invertibleModule_h1_finrank_eq_dual_tensor_dualizing_h0
      X h_dimension L :
    Scheme.Hom.cohomologyFinrank X.hom L 1 =
      Scheme.Hom.cohomologyFinrank X.hom
        (Scheme.Modules.dual L ⊗ curveDualizingModule X.hom) 0)

end
