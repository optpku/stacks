module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable (δ : S → ℤ) [IsDimensionFunction δ]
variable (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
variable (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
variable (k : ℤ)

/- The fixed-dimension flat-pullback homomorphism is provided by the shared cycle API. -/
#check (AlgebraicGeometry.CycleGroup.flatPullback δ X Y f r k :
  CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k →+
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (k + (r : ℤ)))

variable (α : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) k)

/- Forgetting the grading agrees with flat pullback of the underlying algebraic cycle. -/
#check (AlgebraicGeometry.CycleGroup.toAlgebraicCycle_flatPullback δ X Y f r k α :
  toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))
      (flatPullback δ X Y f r k α) =
    AlgebraicCycle.flatPullback δ X Y f r (k + (r : ℤ))
      (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) k α))

variable (x : X.left)

/- Coefficients are computed from the scheme-theoretic inverse images of point closures. -/
#check (AlgebraicGeometry.CycleGroup.flatPullback_apply δ X Y f r k α x :
  toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))
      (flatPullback δ X Y f r k α) x =
    ∑ᶠ y : Y.left,
      toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) k α y *
        ((@Scheme.IdealSheafData.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          ((Scheme.PointClosure.reducedStructure y).ideal.comap f.left)
          (X.hom.relativeDimensionFunction δ) (k + (r : ℤ)) :
            AlgebraicCycle.dimensionSubgroup
              (X.hom.relativeDimensionFunction δ) (k + (r : ℤ))) :
          AlgebraicCycle X.left ℤ) x)

end AlgebraicGeometry.CycleGroup
