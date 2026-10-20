/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction maps in sheaf cohomology

This leaf names the contravariant map on cohomology associated to an inclusion of opens. The
special case with ambient open `⊤` is the global restriction map.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology

variable {X : TopCat.{u}}

/-- Restriction on degree-`q` cohomology along an inclusion `U ⊆ V`. -/
@[stacks 0A3G "restriction in sheaf cohomology"]
noncomputable abbrev restriction (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    {U V : Opens X} (hUV : U ≤ V) :
    F.H' q V ⟶ F.H' q U :=
  (F.cohomologyPresheaf q).map (homOfLE hUV).op

/-- Restriction from global degree-`q` cohomology to cohomology on an open subset. -/
@[stacks 0A3G "global restriction in sheaf cohomology"]
noncomputable abbrev globalRestriction (F : X.Sheaf AddCommGrpCat.{u})
    (q : ℕ) (U : Opens X) :
    F.H' q (⊤ : Opens X) ⟶ F.H' q U :=
  restriction F q le_top

/-- Restriction on cohomology along the identity inclusion is the identity. -/
@[simp]
theorem restriction_refl (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ) (U : Opens X) :
    restriction F q (le_refl U) = 𝟙 _ := sorry

/-- Restriction maps in cohomology compose along a chain of open inclusions. -/
theorem restriction_trans (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ)
    {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W) :
    restriction F q hVW ≫ restriction F q hUV =
      restriction F q (hUV.trans hVW) := sorry

/-- Restriction on cohomology is natural in the coefficient sheaf. -/
theorem cohomologyMap_comp_restriction
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (q : ℕ)
    {U V : Opens X} (hUV : U ≤ V) :
    CategoryTheory.Sheaf.cohomologyMap a q V ≫ restriction G q hUV =
      restriction F q hUV ≫ CategoryTheory.Sheaf.cohomologyMap a q U := sorry

/-- Global restriction to the top open is the identity. -/
@[simp]
theorem globalRestriction_top (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ) :
    globalRestriction F q (⊤ : Opens X) = 𝟙 _ := sorry

end TopCat.Sheaf.Cohomology
