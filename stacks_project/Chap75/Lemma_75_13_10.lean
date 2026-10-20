/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe u

/- Lemma 75.13.10 (1): if `S` is a scheme, `X` is an algebraic space over `S`, `L` lies in
`D⁺_QCoh(𝒪_X)`, and `K` is a pseudo-coherent object of `D(𝒪_X)`, then `RHom(K, L)` given by
the right adjoint to canonical derived tensoring by `K` lies in `D_QCoh(𝒪_X)`. -/
@[stacks 0A8A] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.derivedQCoh_of_pseudoCoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (K : ModuleDerived X)
      [(DerivedTensor.Right.functor K).IsLeftAdjoint] (L : DerivedQCoh X),
      IsPseudoCoherent X K →
        (t.plus : ObjectProperty (ModuleDerived X)) L.obj →
          derivedQuasiCoherentModuleProperty X
            ((DerivedTensor.Right.functor K).rightAdjoint.obj L.obj))

/- Lemma 75.13.10 (2): if `S` is a scheme, `X` is an algebraic space over `S`, `L` lies in
`D_QCoh(𝒪_X)`, and `K` is a perfect object of `D(𝒪_X)`, then `RHom(K, L)` given by
the right adjoint to canonical derived tensoring by `K` lies in `D_QCoh(𝒪_X)`. -/
@[stacks 0A8A] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.derivedQCoh_of_perfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (K : ModuleDerived X)
      [(DerivedTensor.Right.functor K).IsLeftAdjoint] (L : DerivedQCoh X),
      ModuleDerived.IsPerfect K →
        derivedQuasiCoherentModuleProperty X
          ((DerivedTensor.Right.functor K).rightAdjoint.obj L.obj))
