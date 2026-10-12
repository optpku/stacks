/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_42_1_Category
public import stacks_project.Chap76.Lemma_76_42_1_Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.42.1 (1): for a Noetherian algebraic space `X` over a scheme `S`
and a quasi-coherent ideal sheaf `I ⊂ 𝒪_X`, the category of coherent formal
modules along `I` is abelian. -/
@[stacks 089P] #check
  (coherentFormalModules_abelian :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I],
      Abelian (CoherentFormalModules X I))

/- Lemma 76.42.1 (2): exactness in the category of coherent formal modules can
be checked after pullback along a surjective étale morphism of Noetherian
algebraic spaces. -/
@[stacks 089P] #check
  (coherentFormalModules_exact_iff_of_surjectiveEtale :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsNoetherian X]
      [IsNoetherian Y] (I : IdealSubobject X) [IsQuasiCoherent I]
      (f : Y ⟶ X) [Etale f] [Surjective f]
      (C : ShortComplex (CoherentFormalModules X I)),
      C.Exact ↔ (C.map (coherentFormalModulesPullback f I)).Exact)

/- Lemma 76.42.1 (3): for a flat morphism `f : X' ⟶ X` of Noetherian algebraic
spaces, stagewise pullback is an exact functor on coherent formal modules. -/
@[stacks 089P] #check
  (coherentFormalModulesPullback_exact_of_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsNoetherian X]
      [IsNoetherian Y] (f : X ⟶ Y) [Flat f] (I : IdealSubobject Y)
      [IsQuasiCoherent I],
      exactFunctor (CoherentFormalModules Y I)
        (CoherentFormalModules X (I.pullback f))
        (coherentFormalModulesPullback f I))
