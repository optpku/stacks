/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.PushforwardComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 76.42.10: A representable proper morphism of Noetherian algebraic spaces
that is an isomorphism away from the closed subspace cut out by `K` admits a map
from `G` to the completed pushforward of `F` whenever the pullback of `G` is
isomorphic to the completion of `F`. One positive power of `K` annihilates both
kernels and cokernels at every positive stage. -/
@[stacks 08BD] #check
  (AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules.exists_map_to_pushforwardCompletion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [Proper f]
      (hf : yoneda.relativelyRepresentable f)
      (J K : IdealSubobject Y) [IsQuasiCoherent J] [IsQuasiCoherent K]
      (h_iso : IsIsoOverOpen f (closedImmersionComplementι (subschemeι K)))
      (G : CoherentFormalModules Y J) (F : Coh X)
      (β : (coherentFormalModulesPullback f J).obj G ≅
        (CoherentCompletion.functor (J.pullback f)).obj F),
      ∃ α : G ⟶ (CoherentCompletion.functor J).obj
          (Modules.coherentPushforwardObj f F),
        CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K α)
