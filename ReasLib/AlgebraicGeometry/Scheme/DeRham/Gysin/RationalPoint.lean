module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalPoint
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.HodgeCup

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.SchemeOverField.RationalPoint

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Gysin

/-- The Hodge fundamental class of a rational point on a smooth separated scheme over a
field. -/
noncomputable def rationalPointFundamentalClass
    {k : Type u} [Field k] (X : SchemeOverField k) (d : ℕ)
    [IsSeparated X.hom] [SmoothOfRelativeDimension d X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    hodgeCohomologyObject X.hom d (d : ℤ) :=
  @hodgeFundamentalClassOne _
    (𝟙_ (SchemeOverField k)).left X.left x.left
    (isClosedImmersion X x)
    (@finitePresentation _ _ X (SmoothOfRelativeDimension.smooth (n := d) (f := X.hom)) _ x)
    X.hom (SmoothOfRelativeDimension.smooth (n := d) (f := X.hom))
    (@isKoszulRegularImmersion _ _ X (SmoothOfRelativeDimension.smooth (n := d) (f := X.hom)) x)
    d (conormalSheafIsFiniteLocallyFreeOfRank X d x)

/-- The rational-point Hodge class is the existing Gysin fundamental class of its underlying
section. -/
theorem rationalPointFundamentalClass_eq
    {k : Type u} [Field k] (X : SchemeOverField k) (d : ℕ)
    [IsSeparated X.hom] [SmoothOfRelativeDimension d X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    rationalPointFundamentalClass X d x =
      @hodgeFundamentalClassOne _
        (𝟙_ (SchemeOverField k)).left X.left x.left
        (isClosedImmersion X x)
        (@finitePresentation _ _ X (SmoothOfRelativeDimension.smooth (n := d) (f := X.hom)) _ x)
        X.hom (SmoothOfRelativeDimension.smooth (n := d) (f := X.hom))
        (@isKoszulRegularImmersion _ _ X
          (SmoothOfRelativeDimension.smooth (n := d) (f := X.hom)) x)
        d (conormalSheafIsFiniteLocallyFreeOfRank X d x) := sorry

/-- The Hodge Gysin image of `1` along a rational point of an irreducible smooth proper
scheme of relative dimension `d` over a field is nonzero. -/
theorem rationalPointFundamentalClass_ne_zero
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IrreducibleSpace X.left] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    rationalPointFundamentalClass X d x ≠ 0 := sorry

end AlgebraicGeometry.Scheme.DeRham.Gysin

end
