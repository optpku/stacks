module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension.LocallyAlgebraic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The first projection from a product of schemes over a field is flat. -/
theorem flatProdFst (X Y : SchemeOverField k) :
    Flat (Over.Hom.left (prod.fst : X ⨯ Y ⟶ X)) := sorry

/-- The second projection from a product of schemes over a field is flat. -/
theorem flatProdSnd (X Y : SchemeOverField k) :
    Flat (Over.Hom.left (prod.snd : X ⨯ Y ⟶ Y)) := sorry

/-- The dimension of a variety over a field, measured at its generic point. -/
noncomputable def dimension (X : SchemeOverField k) [Variety X] : ℕ :=
  Int.toNat (X.hom.relativeDimensionFunction (fun _ ↦ 0) (genericPoint X.left))

/-- The relative-dimension function at the generic point equals the integer-valued
dimension of the variety. -/
theorem dimension_spec (X : SchemeOverField k) [Variety X] :
    (X.dimension : ℤ) =
      X.hom.relativeDimensionFunction (fun _ ↦ 0) (genericPoint X.left) := sorry

/-- The structure morphism of a variety has the variety's canonical relative dimension. -/
theorem relativeDimensionHomOfVariety (X : SchemeOverField k) [Variety X] :
    Scheme.Hom.RelativeDimension X.hom X.dimension := sorry

/-- The first projection from a product with a variety has the dimension of the
second factor as relative dimension. -/
theorem relativeDimensionProdFst (X Y : SchemeOverField k) [Variety Y] :
    Scheme.Hom.RelativeDimension
      (Over.Hom.left (prod.fst : X ⨯ Y ⟶ X)) Y.dimension := sorry

/-- The second projection from a product with a variety has the dimension of the
first factor as relative dimension. -/
theorem relativeDimensionProdSnd (X Y : SchemeOverField k) [Variety X] :
    Scheme.Hom.RelativeDimension
      (Over.Hom.left (prod.snd : X ⨯ Y ⟶ Y)) X.dimension := sorry

/-- Dimensions of varieties over an algebraically closed field add under products. -/
theorem dimension_prod [IsAlgClosed k] (X Y : SchemeOverField k) [Variety X] [Variety Y] :
    (X ⨯ Y).dimension = X.dimension + Y.dimension := sorry

/-- A product of regular varieties over an algebraically closed field is regular. -/
theorem regularProdOfRegular [IsAlgClosed k]
    (X Y : SchemeOverField k) [Variety X] [Variety Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left] :
    Scheme.Regular (X ⨯ Y).left := sorry

end AlgebraicGeometry.SchemeOverField

end
