module

public import stacks_project.Chap59.Lemma_59_104_1_EtaleSheafDescent
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- Lemma 59.104.6: if `{f i : X_i i ⟶ X}` is an fppf covering family of
schemes, then the functor from Type-valued sheaves on `X.smallEtaleTopology`
to descent data for étale sheaves along that family is an equivalence of
categories. -/
@[stacks 0GF3]
theorem descentIsEquivalenceOfFppfCovering
    {ι : Type v} {X : Scheme.{u}} {X_i : ι → Scheme.{u}}
    (f : ∀ i, X_i i ⟶ X) (h : FppfCovering (fun i ↦ Over.mk (f i))) :
    (pseudofunctor.toDescentData f).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
