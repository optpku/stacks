module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid.PowerSeries
import StacksCheckRecall

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

/- Remark 90.23.3: a prorepresentable groupoid in functors
`(restrictedCoyoneda R0, restrictedCoyoneda R1, s, t, c)` on
`ArtinianLocalAlgCat Λ k` is smooth if and only if `R1` is a power series
ring over `R0` along both inducing maps. Equivalently,
`IsSmooth (restrictedCoyonedaMap s) (restrictedCoyonedaMap t)` if and only
if `IsPowerSeriesOver s` and `IsPowerSeriesOver t`. This follows from
Lemma 90.8.6. -/
@[stacks 06KK] #check (CategoryTheory.GroupoidInFunctors.isSmooth_iff_isPowerSeriesOver :
  ∀ {R0 R1 : CompleteLocalAlgCat Λ k} (s t : R0 ⟶ R1),
    CategoryTheory.GroupoidInFunctors.IsSmooth
        (CompleteLocalAlgCat.restrictedCoyonedaMap s)
        (CompleteLocalAlgCat.restrictedCoyonedaMap t) ↔
      CompleteLocalAlgCat.IsPowerSeriesOver s ∧ CompleteLocalAlgCat.IsPowerSeriesOver t)
