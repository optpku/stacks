/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Basis.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

variable {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)
variable (𝒪 : TopCat.Sheaf CommRingCat.{u} X)

/- Lemma 6.30.13: restriction to the members of a topological basis is an equivalence between
sheaves of modules over `𝒪` and sheaves of modules over the restricted ring sheaf. -/
@[stacks 009U]
#check (BasisSiteSheaf.moduleRestriction_isEquivalence hB
  (TopCat.Sheaf.ringSheafOfComm 𝒪))
