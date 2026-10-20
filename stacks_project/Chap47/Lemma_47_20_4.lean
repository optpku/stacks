/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.ModuleLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/- Lemma 47.20.4 (1): for a finite module over a Noetherian ring with a chosen
dualizing complex, the locus of zero or Cohen–Macaulay localizations is open. -/
@[stacks 0EHS] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.isOpen_cohenMacaulayLocus :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M],
      IsOpen (Module.cohenMacaulayLocus A M))

/- Lemma 47.20.4 (2): the zero-or-Cohen–Macaulay locus of a finite module over a
Noetherian ring with a chosen dualizing complex is dense in the module support. -/
@[stacks 0EHS] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.dense_cohenMacaulayLocus_on_support :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)
      (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M],
      Dense {p : Module.support A M | p.val ∈ Module.cohenMacaulayLocus A M})
