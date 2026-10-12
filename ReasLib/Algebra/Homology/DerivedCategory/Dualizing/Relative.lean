/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/-- A relative dualizing complex for a flat finitely presented commutative algebra `A` over
`R` is an `R`-perfect object `K` of `D(A)` whose derived Hom from the diagonal copy of `A`
to its base change to `A ⊗[R] A` is isomorphic to that diagonal copy. -/
structure IsRelativeDualizingComplex
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) : Prop where
  /-- The complex is perfect relative to `R`. -/
  isPerfectOver : IsPerfectOver R K
  /-- Derived Hom over `A ⊗[R] A` from the diagonal copy of `A` to the base change of `K`
  is isomorphic to the diagonal copy of `A`. -/
  diagonalRHom_isomorphic :
    IsIsomorphic
      (InternalHom.RHom.obj
        (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A))
        ((ModuleCat.derivedExtensionOfScalars
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj K))
      (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A))

namespace IsRelativeDualizingComplex

set_option linter.defProp false in
/-- Construct relative dualizing-complex status from relative perfectness and the diagonal
derived-Hom identification. -/
def ofConditions
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat A)}
    (h_perfect : IsPerfectOver R K)
    (h_diagonal :
      IsIsomorphic
        (InternalHom.RHom.obj
          (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A))
          ((ModuleCat.derivedExtensionOfScalars
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj K))
        (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A))) :
    IsRelativeDualizingComplex R K :=
  ⟨h_perfect, h_diagonal⟩

end IsRelativeDualizingComplex

/-- The two defining conditions for a relative dualizing complex. -/
theorem isRelativeDualizingComplex_iff
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) :
    IsRelativeDualizingComplex R K ↔
      IsPerfectOver R K ∧
        IsIsomorphic
          (InternalHom.RHom.obj
            (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A))
            ((ModuleCat.derivedExtensionOfScalars
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)).obj K))
          (ModuleCat.single0 (Algebra.tensorSquareMultiplicationModule R A)) := sorry

end CategoryTheory.DerivedCategory
