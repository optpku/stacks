/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- An invertible module of degree at least twice the genus on an integral proper curve with
constant global functions is globally generated. -/
@[stacks 0E3C]
theorem isGloballyGenerated_of_curveDegree_ge_two_mul_genus
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (h_degree : 2 * (genus X h_dimension hΓ : ℤ) ≤
      Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L) :
    SheafOfModules.IsGloballyGenerated L := sorry

/-- The degree bound `2 * genus X - 1 + deg Z` ensures global generation for an
invertible module on an integral proper curve with constant global functions. -/
@[stacks 0E3D]
theorem isGloballyGenerated_of_curveDegree_ge_genus_bound
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData) [Nonempty Z.subscheme]
    (hZ_dimension : topologicalKrullDim Z.subscheme = 0)
    (h_degree : 2 * (genus X h_dimension hΓ : ℤ) - 1 +
      (Module.finrank k (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ) ≤
      Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L) :
    SheafOfModules.IsGloballyGenerated L := sorry

/-- For an invertible module on an integral proper curve with constant global
functions, the same degree bound makes restriction to a nonempty zero-dimensional
closed subscheme surjective on global sections. -/
@[stacks 0E3D]
theorem sectionsPullback_surjective_of_curveDegree_ge_genus_bound
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData) [Nonempty Z.subscheme]
    (hZ_dimension : topologicalKrullDim Z.subscheme = 0)
    (h_degree : 2 * (genus X h_dimension hΓ : ℤ) - 1 +
      (Module.finrank k (Scheme.Hom.globalSectionsAlg (Z.subschemeι ≫ X.hom)) : ℤ) ≤
      Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L) :
    Function.Surjective (Scheme.Modules.sectionsPullback Z.subschemeι L) := sorry

/-- An invertible module on a proper reduced connected curve is globally generated if its
degree on every reduced connected one-dimensional closed subscheme is at least twice the
dimension over the base field of the first cohomology of that subscheme's structure sheaf. -/
@[stacks 0E3F]
theorem isGloballyGenerated_of_subschemeDegreeBound
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
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
            hY_dimension.le ((Scheme.Modules.pullback Y.subschemeι).obj L)) :
    SheafOfModules.IsGloballyGenerated L := sorry

end AlgebraicGeometry.SchemeOverField
