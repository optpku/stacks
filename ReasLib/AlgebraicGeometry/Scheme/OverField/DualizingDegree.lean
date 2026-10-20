module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.Complementary
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Properties
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import Mathlib.Topology.KrullDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a proper one-dimensional at-worst-nodal curve with constant global functions and no
rational tail, every proper reduced connected one-dimensional proper subscheme has dualizing
restriction degree at least its first cohomology dimension. -/
theorem dualizingRestrictionDegree_ge_cohomologyFinrank
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X)) :
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
            (dualizingModule X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField
