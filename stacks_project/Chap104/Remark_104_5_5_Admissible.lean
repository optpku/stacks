module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Retract
public import ReasLib.CategoryTheory.Pretriangulated.Admissible
public import ReasLib.CategoryTheory.Pretriangulated.Admissible.Localization
public import ReasLib.CategoryTheory.Pretriangulated.Admissible.Orthogonal
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Left admissibility of parasitic cohomology

Lemma 104.5.4 supplies a colocalization triangle for every object of
`D_{LQCoh^{fbc}}(𝒪_X)`. Consequently the parasitic cohomology subcategory is
left admissible, its left orthogonal `A` is right admissible, and the
composite `A ⥤ D_{LQCoh^{fbc}}(𝒪_X) ⥤ D_QCoh(𝒪_X)` is an equivalence. The
carrier of `DerivedQCoh` remains the Verdier quotient; the subcategory view
is the left orthogonal and the essential image of its inclusion into
`D(X_fppf, 𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The parasitic cohomology subcategory of `D_{LQCoh^{fbc}}(𝒪_X)` is left
admissible. -/
instance derivedParasitic_isLeftAdmissible {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasitic X).IsLeftAdmissible :=
  sorry

/-- The left orthogonal of parasitic cohomology is right admissible in
`D_{LQCoh^{fbc}}(𝒪_X)`. -/
instance derivedParasitic_leftOrthogonal_isRightAdmissible {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (derivedParasitic X).leftOrthogonal.IsRightAdmissible :=
  sorry

namespace DerivedQCoh

/-- The source composition `A ⟶ D_{LQCoh^{fbc}}(𝒪_X) ⟶ D_QCoh(𝒪_X)` from the
left orthogonal of parasitic cohomology to the Verdier quotient. -/
abbrev leftOrthogonalComparison {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasitic X).leftOrthogonal.FullSubcategory ⥤ DerivedQCoh X :=
  (derivedParasitic X).leftOrthogonal.ι ⋙ quotientFunctor X

/-- `leftOrthogonalComparison` is the composite of the left-orthogonal
inclusion with the Verdier quotient functor. -/
theorem leftOrthogonalComparison_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    leftOrthogonalComparison X =
      (derivedParasitic X).leftOrthogonal.ι ⋙ quotientFunctor X :=
  sorry

/-- The comparison `A ⥤ D_QCoh(𝒪_X)` is an equivalence. -/
instance leftOrthogonalComparison.instIsEquivalence {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (leftOrthogonalComparison X).IsEquivalence :=
  sorry

/-- The inclusion of the left orthogonal of parasitic cohomology into
`D(X_fppf, 𝒪_X)`. -/
abbrev leftOrthogonalInclusion {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (derivedParasitic X).leftOrthogonal.FullSubcategory ⥤ ModuleDerived X :=
  (derivedParasitic X).leftOrthogonal.ι ⋙ DerivedLQCohFbc.inclusion X

/-- `leftOrthogonalInclusion` is the composite of the left-orthogonal
inclusion with `DerivedLQCohFbc.inclusion`. -/
theorem leftOrthogonalInclusion_eq {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    leftOrthogonalInclusion X =
      (derivedParasitic X).leftOrthogonal.ι ⋙ DerivedLQCohFbc.inclusion X :=
  sorry

namespace leftOrthogonalInclusion

/-- An object of `D(𝒪_X)` lies in the essential image of
`leftOrthogonalInclusion` iff it is isomorphic to the image of a
left-orthogonal object of `D_{LQCoh^{fbc}}(𝒪_X)`. -/
theorem essImage_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (E : ModuleDerived X) :
    (leftOrthogonalInclusion X).essImage E ↔
      ∃ K : DerivedLQCohFbc X, (derivedParasitic X).leftOrthogonal K ∧
        Nonempty ((DerivedLQCohFbc.inclusion X).obj K ≅ E) :=
  sorry

/-- The essential image of `leftOrthogonalInclusion` is stable under retracts
in `D(X_fppf, 𝒪_X)`. -/
instance essImage_isStableUnderRetracts {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (leftOrthogonalInclusion X).essImage.IsStableUnderRetracts :=
  sorry

end leftOrthogonalInclusion

end DerivedQCoh

end AlgebraicGeometry.AlgebraicStack

