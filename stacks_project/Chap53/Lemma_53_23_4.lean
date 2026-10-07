module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.DualizingDegree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.23.4: for a proper one-dimensional scheme `X` over a field with
`H⁰(X, 𝒪_X) = k`, at-worst-nodal singularities, and no rational tail, every
proper reduced connected one-dimensional closed subscheme `Y ≠ X` satisfies
`deg(ω_X|_Y) ≥ dimₖ H¹(Y, 𝒪_Y)`. -/
@[stacks 0E3J] #check
  (@AlgebraicGeometry.SchemeOverField.dualizingRestrictionDegree_ge_cohomologyFinrank :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : atWorstNodal X)
      (h_no_tail : ¬ Nonempty (RationalTail X)),
      let _ : EquidimensionalSpace X.left :=
        equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension h_global
      let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
      let _ : Fact (atWorstNodal X) := ⟨h_nodal⟩
      ∀ (Y : X.left.IdealSheafData),
        (hY_reduced : IsReduced Y.subscheme) →
        (hY_connected : ConnectedSpace Y.subscheme) →
        (hY_dimension : topologicalKrullDim Y.subscheme = 1) →
        (hY_ne : Y ≠ (⊥ : X.left.IdealSheafData)) →
        (Scheme.Hom.cohomologyFinrank (Y.subschemeι ≫ X.hom)
          (SheafOfModules.unit Y.subscheme.ringCatSheaf : Y.subscheme.Modules) 1 : ℤ) ≤
          Scheme.Modules.curveDegreeOfInvertible (Y.subschemeι ≫ X.hom)
            hY_dimension.le ((Scheme.Modules.pullback Y.subschemeι).obj
              (dualizingModule X.hom)))

end AlgebraicGeometry.SchemeOverField
