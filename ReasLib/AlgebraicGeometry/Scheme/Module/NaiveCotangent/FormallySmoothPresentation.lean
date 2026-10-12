/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Double
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.NaiveCotangent

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.NaiveCotangent

/-- If a scheme morphism factors as an immersion followed by a formally smooth morphism,
its naive cotangent complex is isomorphic in the derived category to the two-term
conormal–differentials complex, with the conormal sheaf in degree `-1`. -/
theorem isomorphicConormalDifferentials {X P Y : Scheme.{u}} (f : X ⟶ Y)
    (i : X ⟶ P) (g : P ⟶ Y) (hfactor : i ≫ g = f) [IsImmersion i]
    [FormallySmooth g] :
    IsIsomorphic
      ((DerivedCategory.Q : CochainComplex X.toRingedSpace.Modules ℤ ⥤
        RingedSpace.ModuleDerived X.toRingedSpace).obj
          (RingedSpace.naiveCotangent f.toShHom))
      ((DerivedCategory.Q : CochainComplex X.toRingedSpace.Modules ℤ ⥤
        RingedSpace.ModuleDerived X.toRingedSpace).obj
          (HomologicalComplex.double (Conormal.Differentials.map i g)
            (ComplexShape.up_mk (-1) 0 (neg_add_cancel 1)))) := sorry

end AlgebraicGeometry.Scheme.Hom.NaiveCotangent
