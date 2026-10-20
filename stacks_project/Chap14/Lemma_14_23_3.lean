module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Homology
import StacksCheckRecall

/-!
# Source-facing recall for Lemma 14.23.3

@stack 0197

The homology computation for the alternating face map complex of an Eilenberg--MacLane object is
owned by ReasLib and exposed here in its two degree cases.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial DoldKan

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (B : A) (k i : ℕ)

/- Lemma 14.23.3 (1): `H_k(s[K(B, k)])` is canonically isomorphic to `B`. -/
@[stacks 0197]
#check (SimplicialObject.eilenbergMacLane.homology.objIso B k :
  (SimplicialObject.eilenbergMacLane.homology.functor (A := A) k k).obj B ≅ B)
#check SimplicialObject.eilenbergMacLane.homology.objIso.hom_naturality
#check SimplicialObject.eilenbergMacLane.homology.objIso.inv_naturality

/- The degree-`k` identification is assembled as a natural isomorphism of coefficient
functors. -/
#check (SimplicialObject.eilenbergMacLane.homology.evalIso (A := A) k)
#check (SimplicialObject.eilenbergMacLane.homology.evalIso_app (A := A) k B)

/- Lemma 14.23.3 (2): `H_i(s[K(B, k)])` vanishes when `i ≠ k`. -/
@[stacks 0197]
#check (SimplicialObject.eilenbergMacLane.homology.isZero B k i :
  i ≠ k → IsZero (K[SimplicialObject.eilenbergMacLane B k].homology i))
#check SimplicialObject.eilenbergMacLane.homology.isZeroFunctor (A := A) k i

end CategoryTheory
