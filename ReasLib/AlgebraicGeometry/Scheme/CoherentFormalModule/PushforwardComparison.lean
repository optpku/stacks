/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.MapAnnihilation
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Proper
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Pullback

/-!
# Comparison with completed coherent pushforward

A formal pullback isomorphism along a proper morphism that is an isomorphism away from a
closed set gives a map to the completed pushforward with uniformly annihilated kernel and
cokernel.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {X Y : Scheme.{u}}

/-- Let `Y` be a Noetherian scheme, let `J` and `K` be quasi-coherent sheaves of
ideals on `Y`, and let `f : X ⟶ Y` be a proper morphism which is an isomorphism over
`V = K.openComplement`. Set `I = J.comap f`. Let `G` be an object of
`CoherentFormalModules Y J`, let `F` be a coherent `𝒪_X`-module, and let
`β : pullbackObj f J G ≅ (CoherentCompletion.functor I).obj F` be an isomorphism in
`CoherentFormalModules X I`. Then there exists a map
`α : G ⟶ (CoherentCompletion.functor J).obj (Modules.coherentPushforwardObj f F)`
in `CoherentFormalModules Y J` whose kernel and cokernel are annihilated by a power of `K`. -/
@[stacks 088B]
theorem exists_map_to_pushforwardCompletion
    [IsNoetherian X] [IsNoetherian Y]
    (J K : Y.IdealSheafData) (f : X ⟶ Y)
    [IsProper f] [IsIso (f ∣_ K.openComplement)]
    (G : CoherentFormalModules Y J) (F : RingedSpace.Coh X.toRingedSpace)
    (β : pullbackObj f J G ≅ (CoherentCompletion.functor (J.comap f)).obj F) :
    ∃ α : G ⟶ (CoherentCompletion.functor J).obj (Modules.coherentPushforwardObj f F),
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K α :=
  sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
