/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedCoextension

/-- For a field `k`, degree-zero cohomology after derived coextension along
`k →+* Polynomial k` is not a finite `Polynomial k`-module. -/
theorem polynomialHomologyNotFinite (k : Type u) [Field k] :
    ¬ Module.Finite (Polynomial k)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u, u} (Polynomial k)) 0).obj
        ((derivedCoextensionOfScalars (algebraMap k (Polynomial k))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u, u} k) 0).obj
            (ModuleCat.of k k)))) := sorry

end CategoryTheory.ModuleCat.DerivedCoextension
