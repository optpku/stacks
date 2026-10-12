/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Uniqueness
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.DerivedTensor.Right.Monoidal
open scoped MonoidalCategory

universe u

/- Lemma 47.15.5: Any two dualizing complexes over a Noetherian commutative ring differ,
up to isomorphism in the derived category, by tensoring with an invertible object. -/
@[stacks 0A7F] #check
  (@CategoryTheory.DerivedCategory.IsDualizingComplex.existsInvertibleTensorIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (T : @CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
        (ModuleCat.{u} A) _ _ _ _ _ _ _)
      {ω ω' : DerivedCategory (ModuleCat.{u} A)}
      (hω : ω.IsDualizingComplex H) (hω' : ω'.IsDualizingComplex H),
      ∃ L : DerivedCategory (ModuleCat.{u} A),
        MonoidalCategory.isInvertibleObject L ∧ Nonempty (ω' ≅ ω ⊗ L))
