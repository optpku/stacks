/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.RingDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/- Lemma 47.17.4 (1): a Noetherian commutative ring admitting a dualizing complex is
universally catenary. -/
@[stacks 0A80] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.universallyCatenaryRing :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
      {ω : DerivedCategory (ModuleCat.{u} A)}, ω.IsDualizingComplex H →
        UniversallyCatenaryRing.{u, u} A)

/- Lemma 47.17.4 (2): a Noetherian commutative ring admitting a dualizing complex has
finite Krull dimension. -/
@[stacks 0A80] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.finiteRingKrullDim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
      {ω : DerivedCategory (ModuleCat.{u} A)}, ω.IsDualizingComplex H →
        FiniteRingKrullDim A)

end CategoryTheory.DerivedCategory.IsDualizingComplex
