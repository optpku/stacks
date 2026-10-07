module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.DualizingModule
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RationalBridge

/- Lemma 53.24.2: for a proper one-dimensional scheme `X` over a field with constant
global functions and at-worst-nodal singularities, the restriction of the dualizing module
to a rational bridge `B` has degree zero. -/
@[stacks 0E64] #check (AlgebraicGeometry.RationalBridge.dualizingRestrictionDegree_eq_zero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom],
      (h_dimension : topologicalKrullDim X.left = 1) →
      (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)) →
      (h_nodal : SchemeOverField.atWorstNodal X) →
      -- Local instance justification (defeq pin): the explicit dimension and global-sections hypotheses are required by the canonical equidimensionality interface used by the degree API.
      letI : EquidimensionalSpace X.left :=
        SchemeOverField.equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective
          X h_dimension h_global
      -- Local instance justification (defeq pin): the explicit dimension equality is required by the canonical dualizing-module invertibility interface.
      letI : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
      -- Local instance justification (defeq pin): the explicit nodality hypothesis is required by the canonical Gorenstein interface.
      letI : Fact (SchemeOverField.atWorstNodal X) := ⟨h_nodal⟩
      -- Local instance justification (search instability): supply X explicitly because projection-based inference does not reliably reconstruct the SchemeOverField owner.
      letI : Scheme.Gorenstein X.left := SchemeOverField.instGorensteinOfAtWorstNodal X
      -- Local instance justification (search instability): supply X explicitly because projection-based inference does not reliably reconstruct the SchemeOverField owner.
      letI : Scheme.Modules.Invertible (curveDualizingModule X.hom) :=
        SchemeOverField.instCurveDualizingModuleInvertible X
      ∀ B : RationalBridge X,
        let L : (componentScheme X B.component).left.Modules :=
          (Scheme.Modules.pullback (X.left.irreducibleComponentSubschemeι B.component)).obj
            (curveDualizingModule X.hom)
        let h_component_dimension :
            topologicalKrullDim (componentScheme X B.component).left ≤ 1 :=
          (Topology.IsInducing.topologicalKrullDim_le
            ((X.left.irreducibleComponentSubschemeι B.component).isClosedEmbedding.isInducing)).trans
            h_dimension.le
        Scheme.Modules.curveDegreeOfInvertible
          (X.left.irreducibleComponentSubschemeι B.component ≫ X.hom)
          h_component_dimension L = 0)

end AlgebraicGeometry.RationalBridge
