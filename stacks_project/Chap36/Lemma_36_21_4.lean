/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.Boundedness
public import stacks_project.Chap36.Lemma_36_21_1

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.21.4: for a quasi-compact and quasi-separated scheme `X`, there is a
uniform integer `N` such that affine-open hypercohomology of `K` supported in `[a, b]`
implies that the coherator of `K` has cohomology supported in `[a, b + N]`. -/
@[stacks 0CSA] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_bounds_of_affineHypercohomology :
    ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
      ∃ N : ℤ, ∀ (K : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ),
        (∀ (U : X.Opens), IsAffineOpen U → ∀ i : ℤ, i ∉ Set.Icc a b →
          IsZero (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U K i)) →
        ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj.IsGE a ∧
          ((Scheme.ModuleDerived.Quasicoherent.inclusion X).rightAdjoint.obj K).obj.IsLE (b + N))

end AlgebraicGeometry.Scheme.DerivedQCoh
