/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Unibranch
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Open
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.10.7 (1): the inclusion of any nonempty open induces a
surjective fundamental-group map at every geometric point of the open. -/
@[stacks 0BQI]
#check (AlgebraicGeometry.Scheme.fundamentalGroupMap_surjective_of_nonemptyOpen :
  {X : Scheme.{u}} → [IrreducibleSpace X] → X.isGeometricallyUnibranch →
  (U : X.Opens) → (U : Set X).Nonempty →
  (Ω : Type u) → [Field Ω] → [IsSepClosed Ω] →
  (s : Spec (.of Ω) ⟶ (U : Scheme)) →
  Function.Surjective (Hom.fundamentalGroupMap U.ι s))

/- Lemma 58.10.7 (2): the actual generic residue-field point morphism is surjective
on fundamental groups under geometric unibranchness. -/
@[stacks 0BQI]
#check (AlgebraicGeometry.Scheme.genericPointInclusion_surjective :
  {X : Scheme.{u}} → [IrreducibleSpace X] → (huni : X.isGeometricallyUnibranch) →
    Function.Surjective (genericPointFundamentalMap X))

end AlgebraicGeometry.Scheme
