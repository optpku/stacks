/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- A scheme morphism to `Spec k` has an invertible module of degree `degree` when some
invertible module has that degree for the canonical curve-degree construction. -/
def HasInvertibleModuleOfDegree (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (degree : ℤ) : Prop :=
  ∃ (L : X.Modules) (hL : Scheme.Modules.Invertible L),
    @Scheme.Modules.curveDegreeOfInvertible k _ X f _ hdim L hL = degree

end AlgebraicGeometry.Scheme.Hom
