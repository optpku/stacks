/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.FinitePresentation

@[expose] public section

open CategoryTheory CommRingCat RingHom

universe u

/-- The property that a commutative algebra over `A` is finitely presented. -/
def IsFinitelyPresentedAlgebra {A : CommRingCat.{u}} (B : Under A) : Prop :=
  FinitePresentation (Hom.hom B.hom)

/-- Finite presentation as an algebra is finite presentation of the structure map. -/
theorem isFinitelyPresentedAlgebra_iff {A : CommRingCat.{u}} (B : Under A) :
    IsFinitelyPresentedAlgebra B ↔ FinitePresentation (Hom.hom B.hom) := sorry

/-- The category of finitely presented commutative algebras over `A`. -/
abbrev FinitelyPresentedAlgebra (A : CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory (fun B : Under A ↦ IsFinitelyPresentedAlgebra B)

/-- An object of `FinitelyPresentedAlgebra A` is finitely presented over `A`. -/
theorem FinitelyPresentedAlgebra.isFinitePresentation
    {A : CommRingCat.{u}} (B : FinitelyPresentedAlgebra A) :
    IsFinitelyPresentedAlgebra B.obj := sorry
