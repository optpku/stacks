/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Cohomology.Noetherian
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.15.2: over a Noetherian commutative ring, if `K` and `L` have finite
cohomology modules in every degree and `L` has finite injective dimension, then
`RHom_A(K, L)` has finite cohomology modules in every degree. -/
@[stacks 0G4H] #check
  (CategoryTheory.DerivedCategory.InternalHom.RHom.finiteCohomology_of_finiteInjectiveDimension :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (K L : _root_.DerivedCategory (ModuleCat.{u} A)),
      CategoryTheory.DerivedCategory.cohomologyIn (ModuleCat.isFG A) K →
        CategoryTheory.DerivedCategory.cohomologyIn (ModuleCat.isFG A) L →
          CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension L →
            CategoryTheory.DerivedCategory.cohomologyIn (ModuleCat.isFG A)
              (CategoryTheory.DerivedCategory.InternalHom.RHom.obj K L))
