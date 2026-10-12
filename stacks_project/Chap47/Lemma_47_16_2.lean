/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.FiniteLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/- Lemma 47.16.2: derived coextension `RHom_A(B, ω)` along a surjective homomorphism
of Noetherian local commutative rings sends a normalized dualizing complex over `A` to one over
`B`. -/
@[stacks 0A7N]
#check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.coextensionOfSurjective :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (f : A →+* B) (hf : Function.Surjective f)
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex HA),
      ((ModuleCat.derivedCoextensionOfScalars f).obj ω).IsNormalizedDualizingComplex HB)

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
