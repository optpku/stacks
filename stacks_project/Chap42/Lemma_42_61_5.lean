/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 42.61.5: the exterior product on total Chow homology of schemes locally of finite
type over a field is associative after pushforward along the canonical product associator. -/
@[stacks 0FBZ] #check (AlgebraicGeometry.ChowGroup.Total.exteriorProduct_assoc :
  {k : Type u} → [Field k] →
    {X Y Z : AlgebraicGeometry.SchemeOverField k} →
    [AlgebraicGeometry.LocallyOfFiniteType X.hom] →
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] →
    [AlgebraicGeometry.LocallyOfFiniteType Z.hom] →
    (alpha : AlgebraicGeometry.ChowGroup.Total (fun _ ↦ 0) X) →
    (beta : AlgebraicGeometry.ChowGroup.Total (fun _ ↦ 0) Y) →
    (gamma : AlgebraicGeometry.ChowGroup.Total (fun _ ↦ 0) Z) →
    AlgebraicGeometry.ChowGroup.Total.map (fun _ ↦ 0)
        (Limits.prod.associator X Y Z).hom
        (AlgebraicGeometry.ChowGroup.Total.exteriorProduct (X ⨯ Y) Z
          (AlgebraicGeometry.ChowGroup.Total.exteriorProduct X Y alpha beta) gamma) =
      AlgebraicGeometry.ChowGroup.Total.exteriorProduct X (Y ⨯ Z) alpha
        (AlgebraicGeometry.ChowGroup.Total.exteriorProduct Y Z beta gamma))
