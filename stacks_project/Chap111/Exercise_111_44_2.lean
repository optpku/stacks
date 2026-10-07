module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.CycleOfCurves
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Exercise 111.44.2: over an algebraically closed field `k`, a projective
1-dimensional `k`-scheme `X` containing a cycle of curves has `H¹(X, 𝒪_X)`
nonzero. -/
@[stacks 0DB5]
#check (AlgebraicGeometry.SchemeOverField.firstCohomology_structureSheaf_not_isZero_of_cycleOfCurves :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Projective X.hom]
    (hXdim : topologicalKrullDim X.left = 1) {n : ℕ}
    (C : Fin n → X.left.IdealSheafData) (x : Fin n → X.left)
    (hΓ : Scheme.IsCycleOfCurves C x),
    ¬ IsZero (Scheme.Hom.cohomology X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1))
