/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap109.Definition_109_22_2_Spaces
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_9_3_HigherDirectImage

/-!
# The object property of stable families of a given genus

`ℳ̄_g` is the full subcategory of stable families of curves for which
`R¹ f_* 𝒪_X` is finite locally free of rank `g`. Together with the stable
locus `ℳ̄`, these are the open DM substacks of `𝒞urves` compared with
`𝒞urves^{DM}` in the source-facing lemma.
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
finite locally free of rank `g`, corresponding to the open substack `ℳ̄_g`. -/
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

/-- The genus-`g` stable locus is contained in the stable locus. -/
theorem stableOfGenus_le_stable (g : ℕ) (S : Scheme.{u}) :
    stableOfGenus g S ≤ stable S :=
  sorry

/-- A stable family of curves lies in at most one of the substacks `ℳ̄_g`. -/
theorem eq_of_mem_stableOfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hg : stableOfGenus g S P) (hg' : stableOfGenus g' S P) : g = g' :=
  sorry

/-- The `stableOfGenus` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_stableOfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (stableOfGenus g S).IsClosedUnderIsomorphisms :=
  sorry

/-- `ℳ̄` is an open DM substack of `𝒞urves`. -/
instance instIsOpenDMSubstack_stable (S : Scheme.{u}) :
    IsOpenDMSubstack (stable S) :=
  sorry

/-- The locus `ℳ̄_g` is an open DM substack of `𝒞urves`. -/
instance instIsOpenDMSubstack_stableOfGenus (g : ℕ) (S : Scheme.{u}) :
    IsOpenDMSubstack (stableOfGenus g S) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
