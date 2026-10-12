/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.FiniteLocallyFreeCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Etale

/- Lemma 37.40.2: a surjective étale morphism `f : U ⟶ S` between affine schemes is
locally dominated by a surjective finite locally free morphism `π : T ⟶ S`; a finite open
cover of `T` has each member factoring through `f`. -/
@[stacks 02LH]
#check (AlgebraicGeometry.Etale.exists_finiteLocallyFreeCover :
  ∀ {U S : Scheme.{u}} (f : U ⟶ S)
    [IsAffine U] [IsAffine S] [Surjective f] [Etale f],
    ∃ (T : Scheme.{u}) (π : T ⟶ S) (_ : Surjective π) (_ : IsFiniteLocallyFree π)
      (n : ℕ) (V : Fin n → T.Opens),
      TopologicalSpace.IsOpenCover V ∧
        ∀ i, ∃ g : (V i).toScheme ⟶ U, g ≫ f = (V i).ι ≫ π)

end AlgebraicGeometry.Etale
