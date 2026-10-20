/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 51.12.3: if a power of `J` annihilates the degree-`p` cohomology of the
structure sheaf on `Spec(A) \ V(I)`, then some power of `J`, depending on `F`, annihilates
the degree-`p` cohomology of every finite locally free module sheaf `F` on that open. -/
@[stacks 0BM5] #check
  (@AlgebraicGeometry.Scheme.Modules.cohomology_isAnnihilatedByPower_of_finiteLocallyFree :
    {A : Type u} → [CommRing A] → (J I : Ideal A) → J ≤ I → J.FG → I.FG → (p : ℕ) →
      (let U := (Scheme.idealSheafDataOfIdealOnSpec I).openComplement
       let JU := Ideal.map
         (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ U.ι.appTop).hom) J
       Module.IsAnnihilatedByPower JU
           (AlgebraicGeometry.Scheme.Modules.cohomology
             (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules) p) →
         ∀ (F : U.toScheme.Modules) [F.IsFiniteLocallyFree],
           Module.IsAnnihilatedByPower JU
             (AlgebraicGeometry.Scheme.Modules.cohomology F p)))
