/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat
import StacksCheckRecall

@[expose] public section

/-!
# K-flat complexes on a ringed site

The reusable K-flat owner lives in `ReasLib.Algebra.Homology.CochainComplex.KFlat`.  This chapter
entry preserves the textbook recall surface while keeping the definition out of the numbered
chapter namespace.
-/

open CategoryTheory

noncomputable section

namespace SheafOfModules.RingedSite

/- Definition 21.17.2: a cochain complex `K` of `𝒪`-modules on a ringed site `(C, 𝒪)` is K-flat
if for every acyclic cochain complex `F`, the totalized tensor product `Tot(F ⊗ K)` is acyclic. -/
@[stacks 06YN] #check @CochainComplex.IsKFlat

#check @CochainComplex.isKFlat_iff

end SheafOfModules.RingedSite
