/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.42.1 (1): for a Noetherian algebraic space `X` over a scheme `S`
and a quasi-coherent ideal sheaf `I ⊂ 𝒪_X`, the category of coherent formal
modules along `I` is abelian. -/
@[stacks 089P] #check
  (AlgebraicGeometry.AlgebraicSpace.coherentFormalModules_abelian :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (I : IdealSubobject X) [IsQuasiCoherent I],
      Abelian (CoherentFormalModules X I))

/- Lemma 76.42.1 (2): exactness in the category of coherent formal modules can
be checked after pullback along a surjective étale morphism of Noetherian
algebraic spaces. -/
@[stacks 089P] #check
  (AlgebraicGeometry.AlgebraicSpace.coherentFormalModules_exact_iff_of_surjectiveEtale :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsNoetherian X]
      [IsNoetherian Y] (I : IdealSubobject X) [IsQuasiCoherent I]
      (f : Y ⟶ X) [Etale f] [Surjective f]
      (C : ShortComplex (CoherentFormalModules X I)),
      C.Exact ↔ (C.map (coherentFormalModulesPullback f I)).Exact)

/- Lemma 76.42.1 (3): for a flat morphism `f : X' ⟶ X` of Noetherian algebraic
spaces, stagewise pullback is an exact functor on coherent formal modules. -/
@[stacks 089P] #check
  (AlgebraicGeometry.AlgebraicSpace.coherentFormalModulesPullback_exact_of_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsNoetherian X]
      [IsNoetherian Y] (f : X ⟶ Y) [Flat f] (I : IdealSubobject Y)
      [IsQuasiCoherent I],
      exactFunctor (CoherentFormalModules Y I)
        (CoherentFormalModules X (I.pullback f))
        (coherentFormalModulesPullback f I))
