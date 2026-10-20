/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.CohenMacaulayRing
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/- Lemma 47.20.2 - the normalized dualizing-complex Cohen--Macaulay equivalence. -/
@[stacks 0AWS] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.cohenMacaulay_tfae :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H),
      let d := ((ringKrullDim A).unbotD 0).toNat
      List.TFAE
        [ Module.CohenMacaulay A A
        , ∃ i : ℤ, DerivedCategory.concentrated (ModuleCat.{u} A) i ω
        , Nonempty
            (ω ≅ ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (dualizingModule H ω hω))⟦(d : ℤ)⟧)
        ])

/- The maximal Cohen--Macaulay consequence for the promoted dualizing module. -/
#check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.dualizingModuleMaximalCohenMacaulay :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H)
      [Module.CohenMacaulay A A],
      Module.MaximalCohenMacaulay A (dualizingModule H ω hω))

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

end
