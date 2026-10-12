/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_23_1
public import stacks_project.Chap90.Lemma_90_8_6_Coyoneda
public import stacks_project.Chap90.Lemma_90_8_6_PowerSeries

/-!
# Smoothness of prorepresentable groupoids in functors

A prorepresentable groupoid in functors on `ArtinianLocalAlgCat Λ k` is smooth if
and only if the representing complete local algebra is a power series ring along
both structure maps.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Remark 90.23.3: a prorepresentable groupoid in functors
`(restrictedCoyoneda R0, restrictedCoyoneda R1, s, t, c)` on
`ArtinianLocalAlgCat Λ k` is smooth if and only if `R1` is a power series
ring over `R0` along both inducing maps. Equivalently,
`IsSmooth (restrictedCoyonedaMap s) (restrictedCoyonedaMap t)` if and only
if `IsPowerSeriesOver s` and `IsPowerSeriesOver t`. This follows from
Lemma 90.8.6. -/
@[stacks 06KK]
theorem isSmooth_iff_isPowerSeriesOver {R0 R1 : CompleteLocalAlgCat Λ k}
    (s t : R0 ⟶ R1) :
    IsSmooth (restrictedCoyonedaMap s) (restrictedCoyonedaMap t) ↔
      IsPowerSeriesOver s ∧ IsPowerSeriesOver t :=
  sorry

end CategoryTheory.GroupoidInFunctors
