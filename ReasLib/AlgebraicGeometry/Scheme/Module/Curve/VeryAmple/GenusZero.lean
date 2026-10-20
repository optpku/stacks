/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.GenusZero
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open ProjectiveSpace.VectorSpace.LinearSystem
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A positive-degree invertible module on a proper genus-zero curve with only constant global
sections is relatively very ample. -/
theorem relativelyVeryAmple_of_genus_zero_of_positive_degree
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (d : ℕ)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le L = (d : ℤ))
    (h_positive : 0 < d) :
    RelativelyVeryAmple X.hom L := sorry

/-- A positive-degree invertible module on a proper genus-zero curve with only constant global
sections admits a basis whose complete linear system is a closed immersion into projective space. -/
theorem exists_basis_closedImmersion_projectiveSpace_of_genus_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [Curve X] [IsProper X.hom]
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_genus : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = 0)
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (d : ℕ)
    (h_degree : Scheme.Modules.curveDegreeOfInvertible X.hom
      (topologicalKrullDim_eq_one X).le L = (d : ℤ))
    (h_positive : 0 < d) :
    ∃ (b : Module.Basis (Fin (d + 1)) k (globalSectionsMod X L))
      (i : X.left ⟶ ProjectiveSpace.scheme k d),
      BasisMorphismSpec d b X L (𝟙 (globalSectionsMod X L)) i ∧
        IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec k d = X.hom := sorry

end AlgebraicGeometry.SchemeOverField
