/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Equivalence
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped DerivedCategory.CohomologyIn

universe u

/- Lemma 47.15.4: an A-linear self-equivalence of the bounded derived category of finitely
generated modules over a Noetherian commutative ring sends the regular object to a
tensor-invertible object in the ambient derived category. -/
@[stacks 0A7E] #check
  (@CategoryTheory.DerivedCategory.isInvertibleObject_image_regular :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
      (F : Dᵇ[ModuleCat.isFG A] ⥤ Dᵇ[ModuleCat.isFG A])
      [Functor.Linear A F] [F.IsEquivalence]
      [MonoidalCategory (DerivedCategory (ModuleCat A))]
      (T : @CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model
        (ModuleCat A) _ _ _ _ _ _ _),
      MonoidalCategory.isInvertibleObject
        ((CategoryTheory.DerivedCategory.Bounded.CohomologyIn.ambient
          (ModuleCat.isFG A)).obj
          (F.obj (CategoryTheory.DerivedCategory.Bounded.CohomologyIn.ringSingle A))))
