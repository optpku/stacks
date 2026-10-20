/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- The genus-`g` stable locus is contained in the stable locus. -/
theorem stableOfGenus_le_stable (g : ℕ) (S : Scheme.{u}) :
    stableOfGenus g S ≤ stable S :=
  sorry

/-- Over a nonempty base, the genus of a stable family of curves is unique. -/
theorem eq_of_mem_stableOfGenus {S : Scheme.{u}} {P : Obj S}
    [Nonempty (base P).left] {g g' : ℕ}
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
