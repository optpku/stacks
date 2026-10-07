module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap109.Definition_109_21_2_Spaces
public import stacks_project.Chap109.Lemma_109_9_3_HigherDirectImage

/-!
# The object property of semistable families of a given genus

`𝒞urves^{semistable}_g` is the full subcategory of semistable families of
curves for which `R¹ f_* 𝒪_X` is finite locally free of rank `g`.
Membership is the source-facing packaging of a classifying morphism
factoring through that open-and-closed substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of semistable families of curves with `R¹ f_* 𝒪_X`
finite locally free of rank `g`, corresponding to the open-and-closed
substack `𝒞urves^{semistable}_g`. -/
def semistableOfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    semistable S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `semistableOfGenus g` means the family is semistable and
`R¹ f_* 𝒪_X` is finite locally free of rank `g`. -/
theorem semistableOfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    semistableOfGenus g S P ↔
      semistable S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Membership in `semistableOfGenus g` implies membership in `semistable`. -/
theorem semistableOfGenus_le_semistable (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    semistableOfGenus g S P → semistable S P :=
  sorry

/-- A semistable family of curves lies in at most one of the substacks
`𝒞urves^{semistable}_g`. -/
theorem eq_of_mem_semistableOfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hg : semistableOfGenus g S P) (hg' : semistableOfGenus g' S P) :
    g = g' :=
  sorry

/-- A family of curves is semistable if and only if it lies in
`semistableOfGenus g` for some `g ≥ 1`. -/
theorem mem_semistable_iff_exists_semistableOfGenus {S : Scheme.{u}}
    (P : Obj S) :
    semistable S P ↔ ∃ g : ℕ, semistableOfGenus (g + 1) S P :=
  sorry

/-- The `semistableOfGenus` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_semistableOfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (semistableOfGenus g S).IsClosedUnderIsomorphisms :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
