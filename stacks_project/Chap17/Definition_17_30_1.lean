/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Algebraic.DeRham
import StacksCheckRecall

@[expose] public section

/- Definition 17.30.1 (0FKM): the relative de Rham complex of a morphism of commutative ring
sheaves on a topological space. -/
@[stacks 0FKM]
#check @TopCat.Sheaf.DeRham.complex
#check @TopCat.Sheaf.DeRham.complex_X
#check @TopCat.Sheaf.DeRham.complex_d
#check @TopCat.Sheaf.DeRham.d_sq

/- Equation 17.30.1.1 (0FKN): the differential sends
`b₀ db₁ ∧ ... ∧ dbₚ` to `db₀ ∧ db₁ ∧ ... ∧ dbₚ`. -/
#check @TopCat.Sheaf.DeRham.d_basic
