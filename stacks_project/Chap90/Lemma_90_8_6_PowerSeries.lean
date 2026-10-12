/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_28_2_FormalHomotopy

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

/-- A morphism `f : R ⟶ S` exhibits `S` as a power series ring over `R` if there is
`n : ℕ` and an isomorphism `e : S ≅ R.mvPowerSeries n` with
`f ≫ e.hom = R.mvPowerSeriesC n`. -/
def IsPowerSeriesOver {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) : Prop :=
  ∃ n : ℕ, ∃ e : S ≅ R.mvPowerSeries n, f ≫ e.hom = R.mvPowerSeriesC n

/-- Being a power series over `R` unpacks to a finite-variable isomorphism over the
canonical coefficient inclusion. -/
theorem isPowerSeriesOver_iff {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    IsPowerSeriesOver f ↔
      ∃ n : ℕ, ∃ e : S ≅ R.mvPowerSeries n, f ≫ e.hom = R.mvPowerSeriesC n :=
  sorry

/-- An isomorphism onto `R.mvPowerSeries n` over `R.mvPowerSeriesC n` exhibits a
power series morphism. -/
theorem IsPowerSeriesOver.of_iso {R S : CompleteLocalAlgCat Λ k} {n : ℕ} {f : R ⟶ S}
    (e : S ≅ R.mvPowerSeries n) (h : f ≫ e.hom = R.mvPowerSeriesC n) :
    IsPowerSeriesOver f :=
  sorry

/-- The canonical coefficient inclusion `R.mvPowerSeriesC n` is a power series
morphism over `R`. -/
theorem isPowerSeriesOver_mvPowerSeriesC (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    IsPowerSeriesOver (R.mvPowerSeriesC n) :=
  sorry

end CompleteLocalAlgCat
