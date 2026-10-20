module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Properties
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Determinant
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- The degree of a finite locally free module on a proper scheme of dimension at most one
equals the degree of its top exterior power. -/
@[stacks 0DJ5]
theorem curveDegree_eq_curveDegree_topExteriorPower
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (ℰ : X.Modules) (n : ℕ) [IsFiniteLocallyFreeOfRank n ℰ] :
    curveDegree f hdim ℰ n =
      @curveDegree k _ X f _ hdim (Λ[n] ℰ) 1
        (SheafOfModules.RingedSite.ExteriorPower.top_rankOne ℰ n) := sorry

/-- The top exterior power and determinant sheaf of a finite locally free module on a proper
scheme of dimension at most one have the same degree. -/
@[stacks 0DJ5]
theorem curveDegree_topExteriorPower_eq_curveDegree_determinantSheaf
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (ℰ : X.Modules) (n : ℕ) [IsFiniteLocallyFreeOfRank n ℰ] :
    @curveDegree k _ X f _ hdim (Λ[n] ℰ) 1
        (SheafOfModules.RingedSite.ExteriorPower.top_rankOne ℰ n) =
      curveDegree f hdim (det(ℰ)) 1 := sorry

end AlgebraicGeometry.Scheme.Modules
