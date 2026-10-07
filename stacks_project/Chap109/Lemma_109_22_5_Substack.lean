module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import stacks_project.Chap109.Definition_109_22_2_Spaces
public import stacks_project.Chap109.Lemma_109_9_4_Substack

/-!
# The object property of stable families of a given genus

`𝒞urves^{stable}_g` is the full subcategory of stable families of curves
for which `R¹ f_* 𝒪_X` is finite locally free of rank `g`. Membership is
the source-facing packaging of a classifying morphism factoring through
that open-and-closed substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of stable families of curves with `R¹ f_* 𝒪_X`
finite locally free of rank `g`, corresponding to the open-and-closed
substack `𝒞urves^{stable}_g`. -/
def stableOfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    stable S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `stableOfGenus g` means the family is stable and
`R¹ f_* 𝒪_X` is finite locally free of rank `g`. -/
theorem stableOfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    stableOfGenus g S P ↔
      stable S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Membership in `stableOfGenus g` is stability together with
membership in `ofGenus g`. -/
theorem stableOfGenus_iff_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    stableOfGenus g S P ↔ stable S P ∧ ofGenus g S P :=
  sorry

/-- Membership in `stableOfGenus g` implies membership in `stable`. -/
theorem stableOfGenus_le_stable (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    stableOfGenus g S P → stable S P :=
  sorry

/-- Membership in `stableOfGenus g` implies membership in `ofGenus g`. -/
theorem stableOfGenus_le_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    stableOfGenus g S P → ofGenus g S P :=
  sorry

/-- A stable family of curves lies in at most one of the substacks
`𝒞urves^{stable}_g`. -/
theorem eq_of_mem_stableOfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hg : stableOfGenus g S P) (hg' : stableOfGenus g' S P) :
    g = g' :=
  sorry

/-- A family of curves is stable if and only if it lies in
`stableOfGenus g` for some `g ≥ 2`. -/
theorem mem_stable_iff_exists_stableOfGenus {S : Scheme.{u}}
    (P : Obj S) :
    stable S P ↔ ∃ g : ℕ, stableOfGenus (g + 2) S P :=
  sorry

/-- The `stableOfGenus` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_stableOfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (stableOfGenus g S).IsClosedUnderIsomorphisms :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
