/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.MapAnnihilation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Proper

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules

/-- For a representable proper morphism of Noetherian algebraic spaces that is
an isomorphism away from the closed subspace cut out by `K`, an isomorphism
between the pullback of a coherent formal module `G` and the completion of a
coherent module `F` yields a morphism from `G` to the completion of `f_* F`.
One positive power of `K` annihilates both the kernels and the cokernels at
every positive stage of this morphism. -/
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
      CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K α := sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules
