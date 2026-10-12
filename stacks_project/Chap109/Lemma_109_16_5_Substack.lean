/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import stacks_project.Chap109.Lemma_109_16_3_Substack
public import stacks_project.Chap109.Lemma_109_9_4_Substack

/-!
# The object property of smooth families of a given genus

`𝒞urves^{smooth, h0}_g` is the full subcategory of smooth families of
curves with universally trivial `𝒪_S ⟶ f_* 𝒪_X` for which
`R¹ f_* 𝒪_X` is finite locally free of rank `g`. Membership is the
source-facing packaging of a classifying morphism factoring through that
open-and-closed substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The object property of smooth families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X`, fibres of dimension `1`, and `R¹ f_* 𝒪_X` finite locally
free of rank `g`, corresponding to the open-and-closed substack
`𝒞urves^{smooth, h0}_g`. -/
def smoothH0OfGenus (g : ℕ) (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    smoothH0 S P ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P))

/-- Membership in `smoothH0OfGenus g` means the family lies in
`smoothH0` and `R¹ f_* 𝒪_X` is finite locally free of rank `g`. -/
theorem smoothH0OfGenus_iff (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P ↔
      smoothH0 S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Membership in `smoothH0OfGenus g` is membership in `smoothH0` together
with membership in `ofGenus g`. -/
theorem smoothH0OfGenus_iff_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P ↔ smoothH0 S P ∧ ofGenus g S P :=
  sorry

/-- Membership in `smoothH0OfGenus g` implies membership in `smoothH0`. -/
theorem smoothH0OfGenus_le_smoothH0 (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P → smoothH0 S P :=
  sorry

/-- Membership in `smoothH0OfGenus g` implies membership in `ofGenus g`. -/
theorem smoothH0OfGenus_le_ofGenus (g : ℕ) {S : Scheme.{u}} (P : Obj S) :
    smoothH0OfGenus g S P → ofGenus g S P :=
  sorry

/-- A smooth family of curves with universally trivial pushforward of `𝒪`
lies in at most one of the substacks `𝒞urves^{smooth, h0}_g`. -/
theorem eq_of_mem_smoothH0OfGenus {S : Scheme.{u}} {P : Obj S} {g g' : ℕ}
    (hg : smoothH0OfGenus g S P) (hg' : smoothH0OfGenus g' S P) : g = g' :=
  sorry

/-- The `smoothH0OfGenus` property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_smoothH0OfGenus
    (g : ℕ) (S : Scheme.{u}) :
    (smoothH0OfGenus g S).IsClosedUnderIsomorphisms :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
