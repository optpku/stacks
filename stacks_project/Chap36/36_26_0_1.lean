/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

variable
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] (σ : (A ⊗[R] R') →+* A')
    (KBase : DerivedCategory (ModuleCat (A ⊗[R] R')))
    (K' : DerivedCategory (ModuleCat A'))
    (α : (ModuleCat.derivedExtensionOfScalars σ).obj KBase ⟶ K') (i : ℤ)

/- 36.26.0.1: For the local tensor-product ring
`B = 𝒪_{X,x} ⊗[𝒪_{S,s}] 𝒪_{S',s'}`, the canonical morphism is
`H^i(K_x ⊗^L_{𝒪_{S,s}} 𝒪_{S',s'}) ⊗[B] 𝒪_{X',x'} ⟶ H^i(K'_{x'})`. -/
@[stacks 0DJ7] #check
  (CategoryTheory.ModuleCat.cohomologyBaseChangeMap σ KBase K' α i :
    (ModuleCat.extendScalars σ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat (A ⊗[R] R')) i).obj KBase) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat A') i).obj K')

end
