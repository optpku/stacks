module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Graph
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Graph line bundles on smooth relative curves

For a separated smooth morphism of relative dimension one, the graph of an
`S`-point is Cartier. Its line bundle on `T ×ₛ X` supplies the point-level
Abel class. No properness, ground field, Hilbert scheme or Picard scheme is
needed. The graph itself is owned by the weaker `Graph` interface.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
noncomputable section
universe u
namespace AlgebraicGeometry.SchemeOver
variable {S : Scheme.{u}} {X T : Over S}

/-- On a separated smooth relative curve, the graph is an effective Cartier divisor. -/
instance graphIdeal_isEffectiveCartier [IsSeparated X.hom]
    [SmoothOfRelativeDimension 1 X.hom] (x : T ⟶ X) :
    IsEffectiveCartierDivisor (graphIdeal x).subschemeι := by
  sorry

/-- The graph divisor's associated line bundle, written on `T ×ₛ X`. -/
noncomputable def graphLineBundle [IsSeparated X.hom]
    [SmoothOfRelativeDimension 1 X.hom] (x : T ⟶ X) : (T ⊗ X).left.Modules :=
  (Scheme.Modules.pullback (β_ T X).hom.left).obj
    (@Scheme.IdealSheafData.associatedSheaf _ (graphIdeal x)
      (graphIdeal_isEffectiveCartier x))

/-- The graph divisor's line bundle is tensor-invertible. -/
instance graphLineBundle_invertible [IsSeparated X.hom]
    [SmoothOfRelativeDimension 1 X.hom] (x : T ⟶ X) :
    Scheme.Modules.Invertible (graphLineBundle x) := by
  sorry

end AlgebraicGeometry.SchemeOver
