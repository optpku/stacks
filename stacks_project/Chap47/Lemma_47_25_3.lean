/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FieldExtension

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/- Lemma 47.25.3 -/
@[stacks 0E0P] #check (CategoryTheory.DerivedCategory.IsDualizingComplex.baseChange_of_fieldExtension :
    ∀ {k K A : Type u} [Field k] [Field K] [Algebra k K]
      [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} (A ⊗[k] K)))]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A)))
      (HAK : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} (A ⊗[k] K))))
      (ω : DerivedCategory (ModuleCat.{u, u} A)),
      let hA : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
      let hAK : IsNoetherianRing (A ⊗[k] K) :=
        Algebra.FiniteType.isNoetherianRing_tensor_left
      @DerivedCategory.IsDualizingComplex A _ hA _ ω HA →
        @DerivedCategory.IsDualizingComplex (A ⊗[k] K) _ hAK _
          ((ModuleCat.derivedExtensionOfScalars
            (algebraMap A (A ⊗[k] K))).obj ω) HAK)

end CategoryTheory.DerivedCategory.IsDualizingComplex
