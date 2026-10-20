module

public import ReasLib.AlgebraicTopology.SimplicialSet.Splitting
import StacksCheckRecall

/-!
@stack 017R
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe u

namespace SSet

variable (U : SSet.{u}) (n : ℕ)
variable (s : SimplicialObject.Splitting U)

/- Lemma 14.18.2 (1): every simplicial set has a splitting by subobjects. -/
@[stacks 017R]
#check (SSet.isSplit U : SimplicialObject.IsSplit U)

/- Lemma 14.18.2 (2): the image of the degree-`n` distinguished summand in any splitting is
exactly the subobject of nondegenerate `n`-simplices. -/
@[stacks 017R]
#check (SimplicialObject.Splitting.inclusion_range s n :
  Set.range (s.ι n) = U.nonDegenerate n)

/- Mathlib's canonical witness uses the nondegenerate simplices as its summands. -/
#check (U.splitting : SimplicialObject.Splitting U)

/- Its distinguished degree-`n` summand is definitionally identified with the type of
nondegenerate `n`-simplices. -/
#check (SSet.splitting_N U n : U.splitting.N n = U.nonDegenerate n)

/- The reusable carrier equivalence packages that identification without exposing transports. -/
#check (SSet.splitting.nonDegenerateEquiv U n : U.splitting.N n ≃ U.nonDegenerate n)

/- Its distinguished map is the canonical inclusion of nondegenerate simplices. -/
#check SSet.splitting_ι

/- Every distinguished summand simplex is nondegenerate. -/
#check SimplicialObject.Splitting.inclusion_mem_nonDegenerate s n

/- Any two splittings determine the same degreewise subobject. -/
#check SimplicialObject.Splitting.subobject_eq

end SSet
