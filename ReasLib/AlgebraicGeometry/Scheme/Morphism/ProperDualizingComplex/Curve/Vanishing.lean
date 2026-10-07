module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.SupportDimensionZero
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.DerivedQCoh
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/-- For a proper one-dimensional scheme over a field with the expected global sections, a
coherent exact sequence from the curve dualizing module with vanishing first cohomology of the
quotient either has vanishing first cohomology in the middle or splits as a biproduct. -/
theorem firstCohomology_isZero_or_isomorphic_biprod
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (F Q : X.left.Modules) [F.IsCoherent] [Q.IsCoherent]
    (ι : curveDualizingModule X.hom ⟶ F) (π : F ⟶ Q)
    (h_zero : ι ≫ π = 0)
    (h_exact : (ShortComplex.mk ι π h_zero).Exact) [Epi π]
    (hQ : IsZero (Scheme.Hom.cohomology X.hom Q 1)) :
    IsZero (Scheme.Hom.cohomology X.hom F 1) ∨
      IsIsomorphic F (curveDualizingModule X.hom ⊞ Q) := sorry

/-- For a coherent module with support of topological Krull dimension at most zero, the
vanishing-or-splitting alternative applies to an exact sequence from the curve dualizing module.
-/
theorem firstCohomology_isZero_or_isomorphic_biprod_of_supportDimension_le_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (F Q : X.left.Modules) [F.IsCoherent] [Q.IsCoherent]
    (ι : curveDualizingModule X.hom ⟶ F) (π : F ⟶ Q)
    (h_zero : ι ≫ π = 0)
    (h_exact : (ShortComplex.mk ι π h_zero).Exact) [Epi π]
    (h_support : topologicalKrullDim (RingedSpace.moduleSupport Q) ≤ 0) :
    IsZero (Scheme.Hom.cohomology X.hom F 1) ∨
      IsIsomorphic F (curveDualizingModule X.hom ⊞ Q) := sorry

/-- For a proper one-dimensional scheme over a field with the expected global sections, a
globally generated invertible module that is not trivial has vanishing first cohomology after
tensoring with the curve dualizing module. -/
theorem firstCohomology_tensor_isZero
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    [SheafOfModules.IsGloballyGenerated L]
    (h_nontrivial : ¬ RingedSpace.IsTrivial L) :
    IsZero (Scheme.Hom.cohomology X.hom
      (curveDualizingModule X.hom ⊗ L) 1) := sorry

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
