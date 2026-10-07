module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.GlobalGeneration

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.22.7: for a proper, reduced, connected, one-dimensional scheme `X` over
a field `k`, an invertible module `L` is globally generated when every reduced,
connected, one-dimensional closed subscheme `Y` satisfies the bound given by
`Scheme.Hom.cohomologyFinrank (Y.subschemeι ≫ X.hom)` on its structure sheaf
and `Scheme.Modules.curveDegreeOfInvertible` on the pullback of `L`. -/
@[stacks 0E3F] #check
  (AlgebraicGeometry.SchemeOverField.isGloballyGenerated_of_subschemeDegreeBound :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsReduced X.left] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (h_degree :
      ∀ (Y : X.left.IdealSheafData),
        (hY_reduced : IsReduced Y.subscheme) →
        (hY_connected : ConnectedSpace Y.subscheme) →
        (hY_dimension : topologicalKrullDim Y.subscheme = 1) →
        2 * (Scheme.Hom.cohomologyFinrank (Y.subschemeι ≫ X.hom)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf : Y.subscheme.Modules) 1 : ℤ) ≤
          Scheme.Modules.curveDegreeOfInvertible (Y.subschemeι ≫ X.hom)
            hY_dimension.le ((Scheme.Modules.pullback Y.subschemeι).obj L)),
    SheafOfModules.IsGloballyGenerated L)

end AlgebraicGeometry.SchemeOverField
