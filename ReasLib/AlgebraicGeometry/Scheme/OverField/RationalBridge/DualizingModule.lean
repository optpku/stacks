/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.Contraction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.RiemannRoch
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Properties

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RationalBridge

/-- A rational-bridge contraction identifies the pullback of the target curve dualizing module with the source curve dualizing module. -/
theorem curveDualizingModule_pullback_isomorphic
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : SchemeOverField.atWorstNodal X)
    (B : RationalBridge X) (Y : SchemeOverField k) (c : X ⟶ Y)
    (a : (complementScheme X B.component).left ⟶ Y.left)
    (b : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left) ⟶ Y.left)
    (componentMap : (componentScheme X B.component).left ⟶ Y.left)
    (componentToSpec : (componentScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left))
    (intersectionToSpec : (intersectionScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left))
    (h_contraction :
      B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec) :
    IsIsomorphic
      ((Scheme.Modules.pullback c.left).obj
        (@curveDualizingModule k _ Y.left Y.hom h_contraction.target_proper))
      (curveDualizingModule X.hom) := sorry

/-- The restriction of the dualizing module to a rational bridge on a nodal curve has degree
zero over the ground field. -/
theorem dualizingRestrictionDegree_eq_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : SchemeOverField.atWorstNodal X) :
    -- Local instance justification (defeq pin): the explicit dimension and global-sections hypotheses are required by the canonical equidimensionality interface used by the degree API.
    letI : EquidimensionalSpace X.left :=
      SchemeOverField.equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective
        X h_dimension h_globalSections
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
        h_component_dimension L = 0 := sorry

end AlgebraicGeometry.RationalBridge
