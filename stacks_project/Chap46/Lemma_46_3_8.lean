/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.FiniteFreeExtension
public import stacks_project.Chap46.Lemma_46_3_6_TensorExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor

/- Lemma 46.3.8: given an exact finite-free kernel presentation of `L`, every
morphism from `L` to the tensor-extension functor of an `A`-module extends across
the middle finite-free module. -/
@[stacks 06V0] #check
  (ModuleValuedFunctor.existsFiniteFreeExtension :
    ∀ {A : CommRingCat.{u}} {n m : ℕ}
      {L : ModuleValuedFunctor.bundled.{u, u} A}
      (f : ModuleCat.of A (Fin n → A) ⟶ ModuleCat.of A (Fin m → A))
      (i : L ⟶ (tensorExtensionFunctor A).obj (ModuleCat.of A (Fin n → A)))
      (hi : i ≫ (tensorExtensionFunctor A).map f =
        ((bundledHasZeroMorphisms.{u, u} A).zero L
          ((tensorExtensionFunctor A).obj (ModuleCat.of A (Fin m → A)))).zero)
      (h_exact : Nonempty (IsLimit
        (@KernelFork.ofι _ _ (bundledHasZeroMorphisms.{u, u} A) _ _ _ _ i hi)))
      (M : ModuleCat.{u} A) (φ : L ⟶ (tensorExtensionFunctor A).obj M),
      ∃ g : ModuleCat.of A (Fin n → A) ⟶ M,
        i ≫ (tensorExtensionFunctor A).map g = φ)

end ModuleValuedFunctor
