/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Homology.Plus
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.InverseSystem.Sequential.EventuallyConstant
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.CategoryTheory.Sites.BoundedCohomologyBasis
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology of homotopy limits from a bounded cohomology basis

The tower is kept in the coefficient full subcategory.  Only the homotopy-limit presentation
forgets it to the ambient derived category, so downstream statements retain the information that
each eventual value satisfies the coefficient property.
-/

open CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

universe wι w z v u

namespace CategoryTheory.DerivedCategory.Plus.CohomologyIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max z v}]
variable [HasExt.{max z v} (Sheaf J AddCommGrpCat.{max z v})]
variable (𝒪 : Sheaf J RingCat.{w})
variable (P : ObjectProperty (SheafOfModules.{max z v} 𝒪))
variable [Abelian (SheafOfModules.{max z v} 𝒪)]
variable [ObjectProperty.IsWeakSerreClass P]
variable [HasDerivedCategory (SheafOfModules.{max z v} 𝒪)]

/-- The degree-`j` cohomology tower of a sequential system in `D⁺[P]`, valued in the
coefficient full subcategory `P`. -/
@[stacks 0D6T "cohomology tower in the coefficient subcategory"]
abbrev homologyTower
    (K : SequentialInverseSystem (DerivedCategory.Plus.CohomologyIn P)) (j : ℤ) :
    SequentialInverseSystem P.FullSubcategory :=
  K ⋙ Homology.functor P j

/-- A bounded cohomology basis identifies one cohomology object of a sequential homotopy limit
with the eventual value of the corresponding cohomology tower. -/
@[stacks 0D6T]
theorem homology_isomorphic_at_of_boundedBasis
    (basis : BoundedCohomologyBasis 𝒪 P)
    (Ksys : SequentialInverseSystem (DerivedCategory.Plus.CohomologyIn P))
    (K : DerivedCategory (SheafOfModules.{max z v} 𝒪))
    (hK : HomotopyLimit.IsOf (Ksys ⋙ ambient P) K)
    (j : ℤ) (Hj : P.FullSubcategory)
    (hEventually : (homologyTower 𝒪 P Ksys j).IsEventuallyConstantWithValue Hj) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max z v} 𝒪) j).obj K) Hj.obj := sorry

/-- Lemma 21.25.3 (0D6T): for a tower in `D⁺[P]` with a bounded cohomology basis, every
eventual cohomology value is the corresponding cohomology object of its homotopy limit. -/
@[stacks 0D6T]
theorem homology_isomorphic_of_boundedBasis
    (basis : BoundedCohomologyBasis 𝒪 P)
    (Ksys : SequentialInverseSystem (DerivedCategory.Plus.CohomologyIn P))
    (K : DerivedCategory (SheafOfModules.{max z v} 𝒪))
    (hK : HomotopyLimit.IsOf (Ksys ⋙ ambient P) K)
    (H : ℤ → P.FullSubcategory)
    (hEventually : ∀ j : ℤ,
      (homologyTower 𝒪 P Ksys j).IsEventuallyConstantWithValue (H j)) :
    ∀ j : ℤ,
      IsIsomorphic
        ((DerivedCategory.homologyFunctor (SheafOfModules.{max z v} 𝒪) j).obj K)
          (H j).obj := sorry

end CategoryTheory.DerivedCategory.Plus.CohomologyIn

end
