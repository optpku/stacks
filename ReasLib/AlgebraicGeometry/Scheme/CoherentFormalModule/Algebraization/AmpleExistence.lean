/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.AmpleDepth
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.FiniteLocallyFreeStage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- A coherent formal module with finite locally free stages along an ample Cartier
divisor on a proper Cohen–Macaulay threefold over a field is a coherent completion. -/
theorem isCompletion_of_cohenMacaulay_threefold
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] [IsNoetherian P.left] (L : P.left.Modules)
    [L.Invertible] [L.IsAmple] (s : L.sections)
    [RingedSpace.IsRegularSection L s]
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
    [CohenMacaulay P.left]
    (h_dimension : topologicalKrullDim P.left = 3) :
    (CoherentCompletion.functor (zeroIdealSheaf L s)).essImage F := sorry

/-- A coherent formal module with finite locally free stages along an ample Cartier
divisor on a proper variety of dimension at least three satisfying `(S₃)` over a
field is a coherent completion. -/
theorem isCompletion_of_serreConditionS_three
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] [IsNoetherian P.left] (L : P.left.Modules)
    [L.Invertible] [L.IsAmple] (s : L.sections)
    [RingedSpace.IsRegularSection L s]
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
    (h_dimension : (3 : WithBot ℕ∞) ≤ topologicalKrullDim P.left)
    (h_S3 : satisfiesSerreConditionS P.left 3) :
    (CoherentCompletion.functor (zeroIdealSheaf L s)).essImage F := sorry

/-- A coherent module whose completion along an ample Cartier divisor on a proper
variety over a field has finite locally free stages is finite locally free on an
open neighborhood of the divisor. -/
theorem finiteLocallyFree_on_openNhds_of_completion
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] [IsNoetherian P.left] (L : P.left.Modules)
    [L.Invertible] [L.IsAmple] (s : L.sections)
    [RingedSpace.IsRegularSection L s]
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
    (E : RingedSpace.Coh P.left.toRingedSpace)
    (hE : Nonempty ((CoherentCompletion.functor (zeroIdealSheaf L s)).obj E ≅ F)) :
    ∃ V : (CoherentCompletion.compactSupport (zeroIdealSheaf L s)).openNhds,
      CoherentCompletion.finiteLocallyFree (Scheme.Opens.toScheme (V.val : P.left.Opens))
        ((Scheme.Modules.coherentRestrictFunctor
          (Scheme.Opens.ι (V.val : P.left.Opens))).obj E) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
