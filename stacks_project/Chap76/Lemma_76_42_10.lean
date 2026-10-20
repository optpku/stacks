/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap76.«76_42_2_1_Completion»
public import stacks_project.Chap76.Lemma_76_42_9_Algebraization
public import stacks_project.Chap76.Lemma_76_42_10_Pullback
public import stacks_project.Chap76.Lemma_76_42_10_Pushforward

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules

/-- Lemma 76.42.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
proper morphism of Noetherian algebraic spaces over `S`. Let `J` and `K` be
quasi-coherent sheaves of ideals on `Y`. Assume `f` is an isomorphism over
`V = Y \ V(K)`. Set `I = J.pullback f`. Let `G` be an object of
`CoherentFormalModules Y J`, let `F` be a coherent `𝒪_X`-module, and let
`β : (coherentFormalModulesPullback f J).obj G ≅ (CoherentCompletion.functor I).obj F` be an
isomorphism in `CoherentFormalModules X I`. Then there exists a map
`α : G ⟶ (CoherentCompletion.functor J).obj (Modules.coherentPushforwardObj f F)`
in `CoherentFormalModules Y J` whose kernel and cokernel are annihilated by a
power of `K`. -/
@[stacks 08BD]
theorem exists_map_to_pushforwardCompletion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [Proper f]
    (hf : yoneda.relativelyRepresentable f)
    (J K : IdealSubobject Y) [IsQuasiCoherent J] [IsQuasiCoherent K]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι (subschemeι K)))
    (G : CoherentFormalModules Y J) (F : Coh X)
    (β : (coherentFormalModulesPullback f J).obj G ≅
      (CoherentCompletion.functor (J.pullback f)).obj F) :
    ∃ α : G ⟶ (CoherentCompletion.functor J).obj
        (Modules.coherentPushforwardObj f F),
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules
