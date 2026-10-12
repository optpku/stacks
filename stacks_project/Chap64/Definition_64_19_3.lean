/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap64.Definition_64_19_3_LFunction
public import stacks_project.Chap64.Definition_64_19_3_Stalk
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.Scheme.Etale

/- Definition 64.19.3: if F is a ℚ_[ℓ]-sheaf on a finite-type scheme X over a
finite field k, viewed as a ℤ_[ℓ]-sheaf with geometric stalks F.qellStalk, the
L-function is the Euler product
L(X, F) := ∏_{x ∈ closedPoints X} det(1 - π_x^* T^{deg x} | F_x̄)⁻¹
in PowerSeries ℚ_[ℓ], where deg x = X.hom.residueDegree x, π_x^* is
ZEllSheaf.geometricFrobeniusStalk, and F_x̄ is F.qellStalk at
geometricPointOverClosedPoint. The product converges because there are only
finitely many closed points of each residue degree. -/
@[stacks 03UX] #check ZEllSheaf.lFunction
