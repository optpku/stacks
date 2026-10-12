/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.RightExact
import StacksCheckRecall

public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

universe u

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/- Lemma 46.4.5 (1): a pointwise right-exact tangent functor carries a binary direct sum
to the canonical binary direct sum of its tangent values. -/
@[stacks 06ZB] #check (ModuleValuedFunctor.tangentBiprodIso :
  ∀ (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N₁ N₂ : ModuleCat.{u} B.right),
    F.tangentObj B (N₁ ⊞ N₂) ≅ F.tangentObj B N₁ ⊞ F.tangentObj B N₂)

/- Lemma 46.4.5 (2): the second functorial `B`-module structure on `TF(B, N)` has
scalar action `b • x = TF(B, b • 𝟙 N)(x)`. -/
@[stacks 06ZB] #check (ModuleValuedFunctor.tangentArgument :
  ∀ (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A),
    ModuleCat.{u} B.right ⥤ ModuleCat.{u} B.right)

/- Lemma 46.4.5 (2): the argument-induced scalar action is computed by applying the tangent
functor to the scalar endomorphism `b • 𝟙 N`. -/
@[stacks 06ZB] #check (ModuleValuedFunctor.tangentArgument_smul :
  ∀ (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (b : B.right) (x : (F.tangentArgument hF B).obj N),
    Eq.mp (F.tangentArgument_obj hF B N) (b • x) =
      (F.tangent.fixedBase B).map (b • 𝟙 N)
        (Eq.mp (F.tangentArgument_obj hF B N) x))

/- Lemma 46.4.5 (3): the canonical map `N ⊗[B] F(B) ⟶ TF(B, N)` is linear for
the argument-induced `B`-module structure on its target. -/
@[stacks 06ZB] #check (ModuleValuedFunctor.tensorToTangentArgument :
  ∀ (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right),
    F.tangentTensor.obj B N ⟶ (F.tangentArgument hF B).obj N)

/- Lemma 46.4.5 (3): the re-bundled linear map agrees pointwise with the canonical
tensor-to-tangent map. -/
@[stacks 06ZB] #check (ModuleValuedFunctor.tensorToTangentArgument_apply :
  ∀ (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    (x : F.tangentTensor.obj B N),
    Eq.mp (F.tangentArgument_obj hF B N) (F.tensorToTangentArgument hF B N x) =
      F.tensorToTangentApp B N x)

/- Lemma 46.4.5 (4): for a finitely presented `B`-module `N`, the canonical map
`TF(B, B) ⊗[B] N ⟶ TF(B, N)` is an isomorphism. -/
@[stacks 06ZB] #check (ModuleValuedFunctor.tangentTensorComparisonIsIso :
  ∀ (F : ModuleValuedFunctor.{u, u} A)
    (hF : ∀ B, rightExactFunctor (ModuleCat.{u} B.right) (ModuleCat.{u} B.right)
      (F.tangent.fixedBase B)) (B : Under A) (N : ModuleCat.{u} B.right)
    [Module.FinitePresentation B.right N],
    IsIso (F.tangentTensorComparison hF B N))

end ModuleValuedFunctor
