/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.PushforwardComparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.25.3: A proper morphism that is an isomorphism away from the vanishing locus of
`K` admits a map from a coherent formal system to the completed pushforward of its
algebraization, with kernel and cokernel annihilated by one power of `K`. -/
@[stacks 088B] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.exists_map_to_pushforwardCompletion :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (J K : Y.IdealSheafData) (f : X ⟶ Y)
      [IsProper f] [IsIso (f ∣_ K.openComplement)]
      (G : Scheme.CoherentFormalModules Y J) (F : RingedSpace.Coh X.toRingedSpace)
      (β : Scheme.CoherentFormalModules.pullbackObj f J G ≅
        (Scheme.CoherentCompletion.functor (J.comap f)).obj F),
      ∃ α : G ⟶ (Scheme.CoherentCompletion.functor J).obj
          (Scheme.Modules.coherentPushforwardObj f F),
        Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K α)
