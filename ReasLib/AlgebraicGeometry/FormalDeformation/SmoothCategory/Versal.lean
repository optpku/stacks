module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Classical
public import ReasLib.RingTheory.Smooth.Adic.Basic

/-!
# Versal bases and unobstructedness

For a predeformation category with a versal formal object over a complete local
base, unobstructedness is equivalent to maximal-ideal-adic formal smoothness of
the structure map into the base. In the classical case these conditions are also
equivalent to a finite-variable power-series presentation of the base over the
coefficient ring.
-/

@[expose] public section

open CategoryTheory IsLocalRing ArtinianLocalAlgCat CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- A predeformation category with a versal formal object over `R` is
unobstructed exactly when the structure map into `R` is formally smooth in the
`maximalIdeal R`-adic topology. -/
@[stacks 0DZK]
theorem isUnobstructed_iff_formallySmooth [IsPredeformationCategory p]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    IsUnobstructed p ↔
      (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic
        (maximalIdeal ξ.base.carrier) :=
  sorry

/-- In the classical case, for a predeformation category with a versal formal
object, unobstructedness, maximal-ideal-adic formal smoothness of the structure
map into the base, and a finite-variable power-series presentation of the base
over the coefficients are equivalent. -/
@[stacks 0DZK]
theorem isUnobstructed_tfae_isClassical [IsPredeformationCategory p] [IsClassical Λ k]
    (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    List.TFAE
      [IsUnobstructed p,
        (algebraMap Λ ξ.base.carrier).formally_smooth_for_adic
          (maximalIdeal ξ.base.carrier),
        IsPowerSeriesOver (fromClassical ξ.base)] :=
  sorry

/-- In the classical case, unobstructedness of a predeformation category with a
versal formal object over `R` is equivalent to a finite-variable power-series
presentation of `R` over the coefficients. -/
theorem isUnobstructed_iff_isPowerSeriesOver [IsPredeformationCategory p]
    [IsClassical Λ k] (ξ : FormalObject p) [FormalObject.IsVersal ξ] :
    IsUnobstructed p ↔ IsPowerSeriesOver (fromClassical ξ.base) :=
  sorry

end CategoryTheory.Functor

