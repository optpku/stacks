module

public import stacks_project.Chap61.Definition_61_12_8_Affine
public import stacks_project.Chap07.Definition_7_6_2_Site

/-!
# Small and affine pro-étale sites

The inherited small pro-étale precoverage and the affine standard pro-étale
precoverage of a chosen big pro-étale presentation are sites.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The chosen small pro-étale precoverage satisfies the site axioms. -/
instance smallPrecoverage.instIsSite (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (smallPrecoverage X S).IsSite := sorry

/-- The chosen big affine standard pro-étale precoverage satisfies the site axioms. -/
instance bigAffineStandardPrecoverage.instIsSite
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    (bigAffineStandardPrecoverage X S).IsSite := sorry

/-- Covering sources in the chosen big pro-étale slice of a weakly étale object
remain weakly étale. -/
theorem mem_smallObjects_of_covering (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) {U : smallSite X S} {R : Presieve U.obj}
    (hR : Presieve.overEquiv U.obj R ∈ X.pretopology U.obj.left)
    {V : bigSite X S}
    {f : V ⟶ U.obj} (hf : R f) : smallObjects X S V := sorry

/-- The chosen small pro-étale precoverage has singleton isomorphism covers,
pullbacks of covering arrows, stability under bind, and stability of pullback
families. -/
theorem smallPrecoverage.isSite_spec (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) :
    (smallPrecoverage X S).HasIsos ∧ (smallPrecoverage X S).HasPullbacks ∧
      (smallPrecoverage X S).IsStableUnderBind ∧
      (smallPrecoverage X S).IsStableUnderPullbackArrows := sorry

/-- The chosen big affine standard pro-étale precoverage has singleton isomorphism
covers, pullbacks of covering arrows, stability under bind, and stability of
pullback families. -/
theorem bigAffineStandardPrecoverage.isSite_spec
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    (bigAffineStandardPrecoverage X S).HasIsos ∧
      (bigAffineStandardPrecoverage X S).HasPullbacks ∧
      (bigAffineStandardPrecoverage X S).IsStableUnderBind ∧
      (bigAffineStandardPrecoverage X S).IsStableUnderPullbackArrows := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
