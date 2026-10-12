/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Grothendieck
import StacksCheckRecall

/-!
# Lemma 15.119.7: determinant on projective `K₀`

The reusable owner is `CategoryTheory.ModuleCat.K0.Projective.det`.  The chapter file keeps the
source label while exposing the generator formula and the relation-kernel API directly from
ReasLib.

@stack 0AFX
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.119.7: determinant map from projective `K₀(R)` to `Pic(R)`. -/
@[stacks 0AFX "Lemma 15.119.7: determinant map on projective K₀"]
#check @CategoryTheory.ModuleCat.K0.Projective.det

#check @CategoryTheory.ModuleCat.K0.Projective.detClass
#check @CategoryTheory.ModuleCat.K0.Projective.relations_le_ker_det
#check @CategoryTheory.ModuleCat.K0.Projective.det_of

end
