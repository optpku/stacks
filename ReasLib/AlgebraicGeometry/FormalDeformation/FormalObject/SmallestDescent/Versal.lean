module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.SmallestDescent
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.PowerSeries

/-!
# Versality of smallest descents

Smallest descents of versal formal objects exhibit the target base as a finite
power series extension of the source base, and the source formal object is
versal as well.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace FormalObject.Hom.IsSmallestDescent

/-- A smallest descent of a versal formal object has a base that is a finite
power series extension of the descent source, compatibly with its base map. -/
theorem isPowerSeriesOver [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {ξ ξ' : FormalObject p} [IsVersal ξ] {f : ξ' ⟶ ξ} (hf : Hom.IsSmallestDescent f) :
    IsPowerSeriesOver f.base :=
  sorry

/-- The source of a smallest descent of a versal formal object is itself versal. -/
theorem isVersal [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {ξ ξ' : FormalObject p} [IsVersal ξ] {f : ξ' ⟶ ξ} (hf : Hom.IsSmallestDescent f) :
    IsVersal ξ' :=
  sorry

end FormalObject.Hom.IsSmallestDescent
