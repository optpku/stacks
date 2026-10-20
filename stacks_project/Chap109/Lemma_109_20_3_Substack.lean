module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import stacks_project.Chap109.Definition_109_20_1_Prestable
public import stacks_project.Chap109.Lemma_109_9_4_Substack

/-!
# The object property of prestable families of a given genus

`𝒞urves^{prestable}_g` is the full subcategory of prestable families of
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

/-- The object property of prestable families of curves with `R¹ f_* 𝒪_X`
finite locally free of rank `g`, corresponding to the open-and-closed
substack `𝒞urves^{prestable}_g`. -/
def prestableOfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    prestable S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `prestableOfGenus g` means the family is prestable and
`R¹ f_* 𝒪_X` is finite locally free of rank `g`. -/
theorem prestableOfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P ↔
      prestable S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Membership in `prestableOfGenus g` is prestability together with
membership in `ofGenus g`. -/
theorem prestableOfGenus_iff_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P ↔ prestable S P ∧ ofGenus g S P :=
  sorry

/-- Membership in `prestableOfGenus g` implies membership in `prestable`. -/
theorem prestableOfGenus_le_prestable (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P → prestable S P :=
  sorry

/-- Membership in `prestableOfGenus g` implies membership in `ofGenus g`. -/
theorem prestableOfGenus_le_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    prestableOfGenus g S P → ofGenus g S P :=
  sorry

/-- A prestable family of curves lies in at most one of the substacks
`𝒞urves^{prestable}_g`. -/
theorem eq_of_mem_prestableOfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hg : prestableOfGenus g S P) (hg' : prestableOfGenus g' S P) : g = g' :=
  sorry

/-- A family of curves is prestable if and only if it lies in
`prestableOfGenus g` for some `g`. -/
theorem mem_prestable_iff_exists_prestableOfGenus {S : Scheme.{u}}
    (P : Obj S) :
    prestable S P ↔ ∃ g : ℕ, prestableOfGenus g S P :=
  sorry

/-- The `prestableOfGenus` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_prestableOfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (prestableOfGenus g S).IsClosedUnderIsomorphisms :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace

