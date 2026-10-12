/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Frobenius
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

variable (p : ℕ) [Fact p.Prime]

/- Example 46.4.6 (1): the module-valued functor whose value on `B` is its regular
module with scalar action `b • x = b ^ p * x`. -/
@[stacks 06ZE] #check
  (ModuleValuedFunctor.Frobenius.functor :
    (p : ℕ) → [Fact p.Prime] → ModuleValuedFunctor (CommRingCat.of (ZMod p)))

#check
  (ModuleValuedFunctor.Frobenius.obj_smul :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (b : B.right) → (x : (ModuleValuedFunctor.Frobenius.functor p).obj B) →
      b • x = ((ModuleCat.of B.right B.right).smul (b ^ p)).hom x)

#check
  (ModuleValuedFunctor.Frobenius.map_apply :
    (p : ℕ) → [Fact p.Prime] → {B B' : Under (CommRingCat.of (ZMod p))} →
      (f : B ⟶ B') → (x : (ModuleValuedFunctor.Frobenius.functor p).obj B) →
      (ModuleValuedFunctor.Frobenius.functor p).map f x = f.right.hom x)

/- Example 46.4.6 (2): the fixed-base tangent functor is naturally isomorphic to
restriction of scalars along Frobenius. -/
@[stacks 06ZE] #check
  (ModuleValuedFunctor.Frobenius.tangentIso :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (ModuleValuedFunctor.Frobenius.functor p).tangent.fixedBase B ≅
        ModuleCat.restrictScalars (ModuleValuedFunctor.Frobenius.ringHom p B))

#check
  (ModuleValuedFunctor.Frobenius.tangentIso_hom_app :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (N : ModuleCat B.right) →
      (x : (ModuleValuedFunctor.Frobenius.functor p).tangentObj B N) →
      (ModuleValuedFunctor.Frobenius.tangentIso p B).hom.app N x =
        ((ModuleValuedFunctor.Frobenius.functor p).tangentι B N x).2)

#check
  (ModuleValuedFunctor.Frobenius.tangentIso_inv_app :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (N : ModuleCat B.right) → (n : N) →
      (ModuleValuedFunctor.Frobenius.tangentIso p B).inv.app N n =
        ModuleValuedFunctor.Frobenius.tangentInvValue p B N n)

/- Example 46.4.6 (3): the scalar action induced by functoriality in the module
argument is naturally isomorphic to the ordinary `B`-module structure. -/
@[stacks 06ZE] #check
  (ModuleValuedFunctor.Frobenius.argumentIso :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (ModuleValuedFunctor.Frobenius.functor p).tangentArgument
          (ModuleValuedFunctor.Frobenius.tangentRightExact p) B ≅
        𝟭 (ModuleCat B.right))

#check
  (ModuleValuedFunctor.Frobenius.argumentIso_hom_app :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (N : ModuleCat B.right) →
      (x : ((ModuleValuedFunctor.Frobenius.functor p).tangentArgument
        (ModuleValuedFunctor.Frobenius.tangentRightExact p) B).obj N) →
      (ModuleValuedFunctor.Frobenius.argumentIso p B).hom.app N x =
        ModuleValuedFunctor.Frobenius.tangentHom p B N
          (ModuleValuedFunctor.Frobenius.argumentToTangent p B N x))

#check
  (ModuleValuedFunctor.Frobenius.argumentIso_inv_app :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (N : ModuleCat B.right) → (n : N) →
      (ModuleValuedFunctor.Frobenius.argumentIso p B).inv.app N n =
        ModuleValuedFunctor.Frobenius.tangentToArgument p B N
          (ModuleValuedFunctor.Frobenius.tangentInvValue p B N n))

/- Example 46.4.6 (4): the Frobenius-twisted and ordinary module actions do not
agree for every `ZMod p`-algebra and module. -/
@[stacks 06ZE] #check
  (ModuleValuedFunctor.Frobenius.actionsDiffer :
    (p : ℕ) → [Fact p.Prime] →
      ∃ (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
        (b : B.right) (n : N), ModuleValuedFunctor.Frobenius.ringHom p B b • n ≠ b • n)

/- Example 46.4.6 (5): the canonical tensor-to-tangent map for the argument-induced
module structure is zero. -/
@[stacks 06ZE] #check
  (ModuleValuedFunctor.Frobenius.tensorComparison_eq_zero :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (N : ModuleCat B.right) →
      (ModuleValuedFunctor.Frobenius.functor p).tensorToTangentArgument
        (ModuleValuedFunctor.Frobenius.tangentRightExact p) B N = 0)

#check
  (ModuleValuedFunctor.Frobenius.squareZeroInr_pow :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (N : ModuleCat B.right) → (n : N) →
      (TrivSqZeroExt.inr n : TrivSqZeroExt B.right N) ^ p = 0)

#check
  (ModuleValuedFunctor.Frobenius.tensorToTangent_eq_zero :
    (p : ℕ) → [Fact p.Prime] → (B : Under (CommRingCat.of (ZMod p))) →
      (N : ModuleCat B.right) →
      (ModuleValuedFunctor.Frobenius.functor p).tensorToTangentApp B N = 0)
