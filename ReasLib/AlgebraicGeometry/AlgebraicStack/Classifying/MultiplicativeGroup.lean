module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

open GroupoidAlgebraicSpace GroupoidScheme

/-- The unique point of `[Spec k / 𝔾ₘ]`, as the atlas image of the unique point of
`Spec k`. -/
def classifyingPoint_multiplicativeGroup (k : Type u) [Field k] :
    Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp) :=
  Points.mapSlice
    ((AlgebraicSpace.ofOverSliceEquiv
        (Over.mk (𝟙 (Spec (.of k))))).inv ≫
      SmallQuotient.atlas (ofScheme
        (ofAction (𝔾ₘ[Spec (.of k)]).toGrp
          (GroupScheme.trivialAction (𝔾ₘ[Spec (.of k)]).toGrp))))
    (default : Spec (.of k))

/-- The classifying stack `[Spec k / 𝔾ₘ]` has a unique point. -/
instance instUnique_points_classifying_multiplicativeGroup (k : Type u) [Field k] :
    Unique (Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp)) where
  default := classifyingPoint_multiplicativeGroup k
  uniq := sorry

/-- The stacky dimension of `[Spec k / 𝔾ₘ]` at its unique point
is `-1`. -/
theorem dimensionAt_classifying_multiplicativeGroup (k : Type u) [Field k]
    (x : Points (classifying (𝔾ₘ[Spec (.of k)]).toGrp)) :
    dimensionAt x = ((-1 : ℤ) : EInt) :=
  sorry

/-- The classifying stack `[Spec k / 𝔾ₘ]` has dimension `-1`. -/
theorem dimension_classifying_multiplicativeGroup (k : Type u) [Field k] :
    dimension (classifying (𝔾ₘ[Spec (.of k)]).toGrp) = ((-1 : ℤ) : EInt) :=
  sorry

/-- The classifying stack `[Spec k / 𝔾ₘ]` has strictly smaller dimension than
the scheme `Spec k` viewed as an algebraic stack. -/
theorem dimension_classifying_multiplicativeGroup_lt_dimension_spec
    (k : Type u) [Field k] :
    dimension (classifying (𝔾ₘ[Spec (.of k)]).toGrp) <
      dimension (GroupoidsOver.slice (Over.mk (𝟙 (Spec (.of k))))) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
