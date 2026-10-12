/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic.BaseChange

/-!
# Degrees of vector bundles under field extension

This file records invariance of the degree of a finite locally free module on a proper curve
after extending the base field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable {X : Scheme.{u}} {n : ℕ}

/-- The degree of a finite locally free module of constant rank on a proper scheme of dimension
at most one is unchanged by extension of the base field. -/
@[stacks 0B59]
theorem curveDegree_eq_baseChange_of_fieldExtension
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    (ℰ : X.Modules) [IsFiniteLocallyFreeOfRank n ℰ] :
    curveDegree f hdim ℰ n =
      curveDegree
        (AlgebraicGeometry.FieldExtension.toBase k k' f)
        (AlgebraicGeometry.FieldExtension.topologicalKrullDim_baseChange_le_one f hdim)
        (Scheme.Modules.FieldExtension.baseChange k k' f ℰ) n := sorry

end AlgebraicGeometry.Scheme.Modules
