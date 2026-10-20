/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.FiniteLocallyFreeStage
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Noetherian
public import ReasLib.RingTheory.Depth.Localization
public import ReasLib.Topology.KrullDimension.Local
public import Mathlib.Order.WithBotTop

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.CoherentCompletion

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- For a proper scheme over a field with an ample invertible section, the strict
depth-dimension bound away from its zero scheme gives bijective neighborhood
completion comparisons for all finite locally free coherent modules. -/
theorem neighborhoodFullyFaithful_of_depth
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P x)
        (SchemeOverField.stalkRing P x)) : WithTop ℤ) : WithBot (WithTop ℤ)) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) > (2 : EInt)) :
    NeighborhoodCompletionFullyFaithful (zeroIdealSheaf L s) := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- For a proper scheme over a field with an ample invertible section, the strict
depth-dimension bound away from its zero scheme algebraizes every stagewise finite
locally free coherent formal module on a neighborhood of that zero scheme. -/
theorem existsFiniteLocallyFreeAlgebraization
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple] (s : L.sections)
    (hdepth : ∀ x : P.left, x ∉ Set.range (zeroSchemeι L s) →
      ((WithTop.map Int.ofNat (moduleDepth (SchemeOverField.stalkRing P x)
        (SchemeOverField.stalkRing P x)) : WithTop ℤ) : WithBot (WithTop ℤ)) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({x} : Set P.left))) > (2 : EInt))
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, CoherentFormalModules.IsFiniteLocallyFreeStage F n) :
      ∃ V : (compactSupport (zeroIdealSheaf L s)).openNhds,
        (onFiniteLocallyFree ((zeroIdealSheaf L s).comap
          (P.left.ofRestrict V.val.isOpenEmbedding))).essImage
            ((coherentFormalModulesRestrictionFunctor (zeroIdealSheaf L s) V.val).obj F) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
