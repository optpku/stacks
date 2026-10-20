/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries

/-!
# Power series morphisms in `CompleteLocalAlgCat`

A morphism `f : R ⟶ S` exhibits `S` as a finite-variable power series ring over `R`
when, after an isomorphism of complete local algebras, it becomes the canonical
coefficient inclusion `R.mvPowerSeriesC n`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

#check (CompleteLocalAlgCat.IsPowerSeriesOver :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S), Prop)

#check (CompleteLocalAlgCat.isPowerSeriesOver_iff :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S),
    IsPowerSeriesOver f ↔
      ∃ n : ℕ, ∃ e : S ≅ R.mvPowerSeries n, f ≫ e.hom = R.mvPowerSeriesC n)

#check (CompleteLocalAlgCat.IsPowerSeriesOver.of_iso :
  ∀ {R S : CompleteLocalAlgCat Λ k} {n : ℕ} {f : R ⟶ S}
    (e : S ≅ R.mvPowerSeries n) (h : f ≫ e.hom = R.mvPowerSeriesC n),
    IsPowerSeriesOver f)

#check (CompleteLocalAlgCat.isPowerSeriesOver_mvPowerSeriesC :
  ∀ (R : CompleteLocalAlgCat Λ k) (n : ℕ), IsPowerSeriesOver (R.mvPowerSeriesC n))

end CompleteLocalAlgCat
