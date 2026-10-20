module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.VeryAmple.GenusZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.OverField.DualizingDegree
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Genus
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal.Properties
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.PlaneCurve

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A proper one-dimensional at-worst-nodal curve with constant global functions and no rational
tail of genus zero is an integral plane conic. -/
theorem exists_irreduciblePlaneConic_of_genus_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : genus X h_dimension h_global = 0) :
    ∃ (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
      (F : MvPolynomial (Fin 3) k),
      IsIntegral Z.subscheme ∧
        Nonempty (X ≅ Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)) ∧
        HasHomogeneousEquation 2 Z F ∧ F.totalDegree = 2 := sorry

/-- The inverse dualizing module of a proper one-dimensional at-worst-nodal curve with constant
global functions and no rational tail of genus zero is relatively very ample. -/
theorem inverseDualizingModule_relativelyVeryAmple_of_genus_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : genus X h_dimension h_global = 0) :
    let _ : EquidimensionalSpace X.left :=
      equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension h_global
    let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
    let _ : Fact (atWorstNodal X) := ⟨h_nodal⟩
    RelativelyVeryAmple X.hom
      (Scheme.Modules.tensorPowerInt (dualizingModule X.hom) (-1)) := sorry

/-- The dualizing module of a proper one-dimensional at-worst-nodal curve with constant global
functions and no rational tail of genus one is isomorphic to the structure module. -/
theorem dualizingModule_isomorphic_unit_of_genus_one
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : genus X h_dimension h_global = 1) :
    Nonempty
      (dualizingModule X.hom ≅
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) := sorry

/-- Every integral tensor power of exponent at least two of the dualizing module of a proper
one-dimensional at-worst-nodal curve with constant global functions and no rational tail of genus
at least two is globally generated. -/
theorem dualizingModule_tensorPower_isGloballyGenerated_of_genus_ge_two
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension h_global)
    (m : ℤ) (h_m : (2 : ℤ) ≤ m) :
    let _ : EquidimensionalSpace X.left :=
      equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension h_global
    let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
    let _ : Fact (atWorstNodal X) := ⟨h_nodal⟩
    SheafOfModules.IsGloballyGenerated
      (Scheme.Modules.tensorPowerInt (dualizingModule X.hom) m) := sorry

end AlgebraicGeometry.SchemeOverField
