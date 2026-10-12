/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.AmpleExistence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Example 52.28.6 (1): for a proper variety over a field, an ample invertible
module with a section and a coherent formal module with finite locally free stages,
Cohen--Macaulayness and dimension three imply that the formal module is a coherent
completion. -/
@[stacks 0EL6] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_cohenMacaulay_threefold :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] [IsNoetherian P.left] (L : P.left.Modules)
    [L.Invertible] [L.IsAmple] (s : L.sections)
    [RingedSpace.IsRegularSection L s]
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
    [CohenMacaulay P.left]
    (h_dimension : topologicalKrullDim P.left = 3),
    (CoherentCompletion.functor (zeroIdealSheaf L s)).essImage F)

/- Example 52.28.6 (2): for a proper variety of dimension at least three over a
field satisfying `(S₃)`, every coherent formal module with finite locally free
stages along an ample Cartier divisor is a coherent completion. -/
@[stacks 0EL6] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_serreConditionS_three :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] [IsNoetherian P.left] (L : P.left.Modules)
    [L.Invertible] [L.IsAmple] (s : L.sections)
    [RingedSpace.IsRegularSection L s]
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
    (h_dimension : (3 : WithBot ℕ∞) ≤ topologicalKrullDim P.left)
    (h_S3 : satisfiesSerreConditionS P.left 3),
    (CoherentCompletion.functor (zeroIdealSheaf L s)).essImage F)

/- Example 52.28.6 (3): whenever a coherent module presents the formal module
as its completion, that module is finite locally free on some open neighborhood of
the divisor. -/
@[stacks 0EL6] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.finiteLocallyFree_on_openNhds_of_completion :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    [Variety P] [IsNoetherian P.left] (L : P.left.Modules)
    [L.Invertible] [L.IsAmple] (s : L.sections)
    [RingedSpace.IsRegularSection L s]
    (F : CoherentFormalModules P.left (zeroIdealSheaf L s))
    (h_stage : ∀ n : ℕ, IsFiniteLocallyFreeStage F n)
    (E : RingedSpace.Coh P.left.toRingedSpace)
    (hE : Nonempty ((CoherentCompletion.functor (zeroIdealSheaf L s)).obj E ≅ F)),
    ∃ V : (CoherentCompletion.compactSupport (zeroIdealSheaf L s)).openNhds,
      CoherentCompletion.finiteLocallyFree (Scheme.Opens.toScheme (V.val : P.left.Opens))
        ((Scheme.Modules.coherentRestrictFunctor
          (Scheme.Opens.ι (V.val : P.left.Opens))).obj E))

end AlgebraicGeometry.Scheme.CoherentFormalModules
