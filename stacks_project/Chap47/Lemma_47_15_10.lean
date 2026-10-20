/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Polynomial

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/- Lemma 47.15.10: derived scalar extension of a dualizing complex over a Noetherian
commutative ring `A` along `Polynomial.C : A →+* Polynomial A` is dualizing over
`Polynomial A`. -/
@[stacks 0A7J] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.polynomialExtension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} (Polynomial A)))]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} (Polynomial A))))
      (ω : DerivedCategory (ModuleCat.{u} A)), ω.IsDualizingComplex HA →
        ((ModuleCat.derivedExtensionOfScalars Polynomial.C).obj ω).IsDualizingComplex HB)

end CategoryTheory.DerivedCategory.IsDualizingComplex
