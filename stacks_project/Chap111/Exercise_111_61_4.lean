module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} (X : SchemeOverField k)
    [Curve X] [Projective X.hom] (points : Fin n → X.left)
    (points_injective : Function.Injective points)
    (points_singular : ∀ index, points index ∈ Sing(X.left))

/- Exercise 111.61.4: over an algebraically closed field `k`, if `X` is a projective
curve with `n` pairwise distinct singular points, the genus of its normalization is
at most `-n + dim_k H¹(X, 𝒪_X)`. -/
@[stacks 0ELJ] #check
  (AlgebraicGeometry.SchemeOverField.Normalization.structureSheafH1Finrank_add_n_le
    X points points_injective points_singular :
    Scheme.Hom.cohomologyFinrank (SchemeOverField.normalization X).hom
        (SheafOfModules.unit (SchemeOverField.normalization X).left.ringCatSheaf :
          (SchemeOverField.normalization X).left.Modules) 1 + n ≤
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)

#check
  (AlgebraicGeometry.SchemeOverField.Normalization.structureSheafH1Finrank_le_neg_n_add
    X points points_injective points_singular :
    (Scheme.Hom.cohomologyFinrank (SchemeOverField.normalization X).hom
        (SheafOfModules.unit (SchemeOverField.normalization X).left.ringCatSheaf :
          (SchemeOverField.normalization X).left.Modules) 1 : ℤ) ≤
      -(n : ℤ) +
        Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)
