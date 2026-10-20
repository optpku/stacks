/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

universe u

/- Proposition 50.20.4: a nonempty smooth proper equidimensional scheme over a field admits
 a top-degree de Rham trace whose cup-trace pairings are perfect in every integer degree. -/
@[stacks 0FW7] #check
  (AlgebraicGeometry.Scheme.DeRham.existsDeRhamPoincareTrace :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) (d : ℕ)
      [Nonempty X.left] [Smooth X.hom] [IsProper X.hom] [EquidimensionalSpace X.left]
      [derivedMonoidal : MonoidalCategory
        (AlgebraicGeometry.Scheme.DeRham.coefficientDerived X.hom)]
      [qhMonoidal : Functor.Monoidal
        (DerivedCategory.Qh : HomotopyCategory
          (AlgebraicGeometry.Scheme.DeRham.coefficientModules X.hom) (up ℤ) ⥤
            AlgebraicGeometry.Scheme.DeRham.coefficientDerived X.hom)]
      [globalLaxMonoidal :
        (AlgebraicGeometry.Scheme.DeRham.globalDerivedFunctor X.hom).LaxMonoidal]
      (h_dimension : topologicalKrullDim X.left = d),
      ∃ t : AlgebraicGeometry.Scheme.DeRham.cohomologyOverAffineBase X.hom
          (2 * (d : ℤ)) ⟶ ModuleCat.of k k,
        AlgebraicGeometry.Scheme.DeRham.CohomologyTrace.IsPerfect X.hom d t)

/- Proposition 50.20.4: any two perfect traces differ by precomposition with multiplication
 by a global-function unit. -/
@[stacks 0FW7] #check
  (AlgebraicGeometry.Scheme.DeRham.deRhamPoincareTrace_unique :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) (d : ℕ)
      [Nonempty X.left] [Smooth X.hom] [IsProper X.hom] [EquidimensionalSpace X.left]
      [derivedMonoidal : MonoidalCategory
        (AlgebraicGeometry.Scheme.DeRham.coefficientDerived X.hom)]
      [qhMonoidal : Functor.Monoidal
        (DerivedCategory.Qh : HomotopyCategory
          (AlgebraicGeometry.Scheme.DeRham.coefficientModules X.hom) (up ℤ) ⥤
            AlgebraicGeometry.Scheme.DeRham.coefficientDerived X.hom)]
      [globalLaxMonoidal :
        (AlgebraicGeometry.Scheme.DeRham.globalDerivedFunctor X.hom).LaxMonoidal]
      (h_dimension : topologicalKrullDim X.left = d)
      (t t' : AlgebraicGeometry.Scheme.DeRham.cohomologyOverAffineBase X.hom
        (2 * (d : ℤ)) ⟶ ModuleCat.of k k)
      (ht : AlgebraicGeometry.Scheme.DeRham.CohomologyTrace.IsPerfect X.hom d t)
      (ht' : AlgebraicGeometry.Scheme.DeRham.CohomologyTrace.IsPerfect X.hom d t'),
      ∃ u : Γ(X.left, ⊤)ˣ,
        t' = AlgebraicGeometry.Scheme.DeRham.CohomologyTrace.unitAction X.hom
          (2 * (d : ℤ)) u ≫ t)
