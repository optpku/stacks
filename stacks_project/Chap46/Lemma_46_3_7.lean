/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.WeightGrading

universe u

/- Lemma 46.3.7: for a module-valued functor satisfying flat base change, the Laurent weight
submodules form an internal direct sum, and projection through degree zero lands in weight zero. -/
@[stacks 06UZ] #check
  (ModuleValuedFunctor.weightSubmodule_isInternal :
    ∀ {A : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra A B]
      (F : ModuleValuedFunctor.{u, u} A) (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜],
      F.HasFlatBaseChange → DirectSum.IsInternal (F.weightSubmodule 𝒜))

#check
  (ModuleValuedFunctor.degreeZero_image_le_weightZero :
    ∀ {A : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra A B]
      (F : ModuleValuedFunctor.{u, u} A) (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜],
      F.HasFlatBaseChange → ∀ x : F.obj (CommRingCat.mkUnder A B),
        F.map (GradedAlgebra.degreeZeroEnd 𝒜).toUnder x ∈ F.weightSubmodule 𝒜 0)
