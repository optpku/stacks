module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.WContractible
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 61.13.1: let T = Spec(A) be an affine scheme. Then A is w-contractible
if and only if every pro-étale covering of T can be refined by a Zariski
covering of the form T = ∐_{i=1,...,n} U_i. -/
@[stacks 098F] #check
  (IsWContractibleRing.iff_hasFiniteCoproductZariskiRefinement :
    {A : Type u} → [CommRing A] →
      IsWContractibleRing A ↔
        AlgebraicGeometry.Scheme.Proetale.HasFiniteCoproductZariskiRefinement
          (AlgebraicGeometry.Spec (.of A)))
