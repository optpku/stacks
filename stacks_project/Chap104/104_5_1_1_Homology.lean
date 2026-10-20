module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Homology
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Factorization.Homological
public import stacks_project.Chap104.«104_5_1_1_Reflector»
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Cohomology of D_QCoh on an algebraic stack

Degree-`i` cohomology on `DerivedLQCohFbc` composed with the Serre quotient
`Q` inverts the Verdier system of parasitic cohomology, and therefore factors
uniquely through `DerivedQCoh` as a cohomological functor
`H^i : DerivedQCoh X ⥤ FppfModules.LQCohFbc.Quotient X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty CategoryTheory.ObjectProperty.VerdierQuotient
open AlgebraicGeometry.GroupoidsOver
open DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.DerivedQCoh

variable {S : Scheme.{u}}

/-- The composite of lifted cohomology on `DerivedLQCohFbc X` with the Serre
quotient `toQCoh`. -/
def homologyToQCoh (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ) :
    DerivedLQCohFbc X ⥤ FppfModules.LQCohFbc.Quotient X :=
  Homology.functor (FppfModules.lqcohFbc X) i ⋙ FppfModules.LQCohFbc.toQCoh X

/-- `homologyToQCoh X i` is lifted cohomology postcomposed with `toQCoh`. -/
theorem homologyToQCoh_eq (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ) :
    homologyToQCoh X i =
      Homology.functor (FppfModules.lqcohFbc X) i ⋙
        FppfModules.LQCohFbc.toQCoh X := sorry

/-- The composite of lifted cohomology on `DerivedLQCohFbc X` with the Serre
quotient `toQCoh` is homological. -/
instance homologyToQCoh.instIsHomological (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    (homologyToQCoh X i).IsHomological := sorry

/-- Objects with parasitic cohomology lie in the homological kernel of
`homologyToQCoh X i`. -/
theorem derivedParasitic_le_homologicalKernel (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    derivedParasitic X ≤ (homologyToQCoh X i).homologicalKernel := sorry

/-- The composite `homologyToQCoh X i` inverts the Verdier system of parasitic
cohomology. -/
theorem homologyToQCoh_inverts_trW (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    (derivedParasitic X).trW.IsInvertedBy (homologyToQCoh X i) := sorry

/-- 104.5.1.1 The cohomological functor `H^i : D_QCoh(𝒪_X) ⟶ QCoh(𝒪_X)`
obtained by descending `homologyToQCoh X i` along the Verdier quotient by
parasitic cohomology. Here `QCoh(𝒪_X)` is modeled as the Serre quotient
`FppfModules.LQCohFbc.Quotient X`. -/
def homologyFunctor (X : GroupoidsOver S) [AlgebraicStack X] (i : ℤ) :
    DerivedQCoh X ⥤ FppfModules.LQCohFbc.Quotient X :=
  Homological.factor (derivedParasitic X) (homologyToQCoh X i)
    (homologyToQCoh_inverts_trW X i)

/-- `homologyFunctor X i` is a homological functor. -/
instance homologyFunctor.instIsHomological (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    (homologyFunctor X i).IsHomological := sorry

/-- The canonical comparison identifying
`quotientFunctor X ⋙ homologyFunctor X i` with `homologyToQCoh X i`. -/
def homologyFunctor_comp_quotientFunctor (X : GroupoidsOver S)
    [AlgebraicStack X] (i : ℤ) :
    quotientFunctor X ⋙ homologyFunctor X i ≅ homologyToQCoh X i :=
  Homological.factor.facIso (derivedParasitic X) (homologyToQCoh X i)
    (homologyToQCoh_inverts_trW X i)

/-- Strict factorization of `homologyFunctor X i` through
`quotientFunctor X`. -/
theorem homologyFunctor_fac (X : GroupoidsOver S) [AlgebraicStack X]
    (i : ℤ) :
    quotientFunctor X ⋙ homologyFunctor X i = homologyToQCoh X i := sorry

/-- An object of `DerivedQCoh X` is zero if and only if all of its
quasi-coherent cohomology objects vanish. -/
theorem isZero_iff_homology {X : GroupoidsOver S} [AlgebraicStack X]
    (E : DerivedQCoh X) :
    IsZero E ↔ ∀ i : ℤ, IsZero ((homologyFunctor X i).obj E) := sorry

end AlgebraicGeometry.AlgebraicStack.DerivedQCoh
