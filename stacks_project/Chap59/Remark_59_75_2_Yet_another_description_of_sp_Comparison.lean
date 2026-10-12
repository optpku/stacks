/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Comparison

open AlgebraicGeometry Scheme CategoryTheory

universe u

@[expose] public section

noncomputable section

variable {S : Scheme.{u}} (s t : GeometricPoint S)
variable (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
variable (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)

/- The strict-henselization comparison existence and uniqueness API. -/
#check (AlgebraicGeometry.Scheme.existsUnique_strictHenselizationComparison S s t
  (etaleLocalRing S s) (etaleLocalRing S t) point (StrictHenselization.closedPoint t)
  point_over (StrictHenselization.closedPoint_over t) :
  ∃! comparison : strictHenselizationAt S t ⟶ strictHenselizationAt S s,
    comparison ≫ StrictHenselization.toScheme S s = StrictHenselization.toScheme S t ∧
      StrictHenselization.closedPoint t ≫ comparison = point)

end
