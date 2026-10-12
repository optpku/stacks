/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_13_10_InternalHom
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

/- Lemma 75.13.10 (1): if `S` is a scheme, `X` is an algebraic space over `S`, `L` lies in
`D⁺_QCoh(𝒪_X)`, and `K` is a pseudo-coherent object of `D(𝒪_X)`, then `RHom(K, L)` given by
`ihomOf` lies in `D_QCoh(𝒪_X)`. -/
@[stacks 0A8A] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.derivedQCoh_of_pseudoCoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X)) (K : ModuleDerived X) (L : DerivedQCoh X),
      IsPseudoCoherent X K →
        (t.plus : ObjectProperty (ModuleDerived X)) L.obj →
          derivedQuasiCoherentModuleProperty X ((ihomOf H K).obj L.obj))

/- Lemma 75.13.10 (2): if `S` is a scheme, `X` is an algebraic space over `S`, `L` lies in
`D_QCoh(𝒪_X)`, and `K` is a perfect object of `D(𝒪_X)`, then `RHom(K, L)` given by `ihomOf`
lies in `D_QCoh(𝒪_X)`. -/
@[stacks 0A8A] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.derivedQCoh_of_perfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [MonoidalCategory (ModuleDerived X)]
      (H : MonoidalClosed (ModuleDerived X)) (K : ModuleDerived X) (L : DerivedQCoh X),
      ModuleDerived.IsPerfect K →
        derivedQuasiCoherentModuleProperty X ((ihomOf H K).obj L.obj))
