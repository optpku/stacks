/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CoordinateCross.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace.CoordinateCross

noncomputable section

universe u

/- Exercise 111.43.1 (1): if `k` is a field and `X` is the coordinate cross in
`ℙ^n_k`, then `H^0(X, 𝒪_X)` is isomorphic to `k` as a `k`-module. -/
@[stacks 0DAJ] #check
  (AlgebraicGeometry.ProjectiveSpace.CoordinateCross.cohomology_zero :
    ∀ (k : Type u) [Field k] (n : ℕ),
    IsIsomorphic
      (Scheme.Hom.cohomology (toSpec k n)
        (SheafOfModules.unit (scheme k n).ringCatSheaf : (scheme k n).Modules) 0)
      (ModuleCat.of k k))

/- Exercise 111.43.1 (2): if `k` is a field and `X` is the coordinate cross in
`ℙ^n_k`, then `H^i(X, 𝒪_X) = 0` for every `i > 0`. -/
@[stacks 0DAJ] #check
  (AlgebraicGeometry.ProjectiveSpace.CoordinateCross.cohomology_isZero_of_pos :
    ∀ (k : Type u) [Field k] (n i : ℕ), 0 < i →
    IsZero
      (Scheme.Hom.cohomology (toSpec k n)
        (SheafOfModules.unit (scheme k n).ringCatSheaf : (scheme k n).Modules) i))

/- The canonical map from `k` to global sections of the coordinate cross is
bijective. -/
#check (AlgebraicGeometry.ProjectiveSpace.CoordinateCross.globalSectionsMap_bijective :
  ∀ (k : Type u) [Field k] (n : ℕ),
    Function.Bijective (Scheme.Hom.globalSectionsMap (toSpec k n)))
