/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Curve.StableCurves
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.StableDeligneMumford
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

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.stableOfGenus_le_stable :
  ∀ (g : ℕ) (S : Scheme.{u}), stableOfGenus g S ≤ stable S)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.eq_of_mem_stableOfGenus :
  ∀ {S : Scheme.{u}} {P : Obj S}
    [Nonempty (base P).left] {g g' : ℕ}
    (hg : stableOfGenus g S P) (hg' : stableOfGenus g' S P), g = g')

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_stableOfGenus :
  ∀ (g : ℕ) (S : Scheme.{u}), (stableOfGenus g S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsOpenDMSubstack_stable :
  ∀ (S : Scheme.{u}), IsOpenDMSubstack (stable S))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsOpenDMSubstack_stableOfGenus :
  ∀ (g : ℕ) (S : Scheme.{u}), IsOpenDMSubstack (stableOfGenus g S))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
