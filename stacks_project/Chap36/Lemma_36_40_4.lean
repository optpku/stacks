/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Truncation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.40.4: for a perfect derived module `P` on a quasi-compact quasi-separated
scheme, eventual vanishing of `Ext⁽i⁾(P, E.obj)` in negative degrees is equivalent to
eventual vanishing after applying the upper truncation `t.truncLE a` to `E.obj`. -/
@[stacks 0GEM] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.extSubsingletonEventually_iff_truncLE :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      {P : RingedSpace.ModuleDerived X.toRingedSpace},
      RingedSpace.ModuleDerived.IsPerfect P →
        ∀ (E : DerivedCategory.CohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) (a : ℤ),
        (∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ → Subsingleton (Ext⁽i⁾(P, E.obj))) ↔
          ∃ n₀ : ℤ, ∀ i : ℤ, i ≤ n₀ →
            Subsingleton (Ext⁽i⁾(P, (t.truncLE a).obj E.obj)))

end AlgebraicGeometry.Scheme.DerivedQCoh
