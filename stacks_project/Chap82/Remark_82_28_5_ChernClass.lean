/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.OperationalFirstChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjSymChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveBaseChange

/-! Canonical rankwise Chern operations on the actual rational-equivalence quotient.
The implementation is the explicit Proj(Sym) / tautological / Segre construction.
No parallel cycle-as-Chow ring or chosen positive Chern family remains. -/
