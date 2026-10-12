/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Duality
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Invertible

@[expose] public section

open CategoryTheory
open DerivedCategory.DerivedTensor.Right.Monoidal
open scoped MonoidalCategory

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Any two dualizing complexes over a Noetherian commutative ring differ by tensoring with an
invertible object of the derived category. -/
theorem existsInvertibleTensorIso
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (T : @Model (ModuleCat.{u} A) _ _ _ _ _ _ _)
    {ω ω' : DerivedCategory (ModuleCat.{u} A)}
    (hω : ω.IsDualizingComplex H) (hω' : ω'.IsDualizingComplex H) :
    ∃ L : DerivedCategory (ModuleCat.{u} A),
      MonoidalCategory.isInvertibleObject L ∧ Nonempty (ω' ≅ ω ⊗ L) := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
