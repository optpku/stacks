module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian

/-!
# Algebraization from infinitesimal thickenings

This file gives an algebraization criterion for coherent formal modules using equivalences on
all positive-power thickenings and a torsion approximation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.IdealSheafData

noncomputable section

universe u

namespace CoherentCompletionFunctor

/-- A coherent formal module is algebraizable when completion is an equivalence on every
positive-power thickening and it has an approximation whose stagewise kernel and cokernel are
uniformly annihilated by a power of the thickening ideal. -/
theorem mem_essImage_of_thickening_equivalences_and_torsion_approximation
    {X : Scheme.{u}} [IsNoetherian X] {I K : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (ctxThickening : (e : ℕ+) →
      CoherentCompletionFunctor (K ^ (e : ℕ)).subscheme
        (I.comap (K ^ (e : ℕ)).subschemeι))
    (hThickeningEquiv : ∀ e : ℕ+, (ctxThickening e).IsEquivalence)
    (E : Scheme.CoherentFormalModules X I)
    (hApprox : ∃ H : RingedSpace.Coh X.toRingedSpace,
      ∃ alpha : E ⟶ ctx.obj H,
        Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K alpha) :
    ctx.essImage E := sorry

end CoherentCompletionFunctor

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- Lemma 30.25.2 (088A): a coherent formal module is algebraizable when canonical completion
is an equivalence on every positive-power thickening and the module has an approximation with
uniformly ideal-power-torsion stagewise kernel and cokernel. -/
@[stacks 088A "algebraization from canonical completion on thickenings"]
theorem mem_essImage_of_thickening_equivalences_and_torsion_approximation
    {X : Scheme.{u}} [IsNoetherian X] {I K : X.IdealSheafData}
    (hThickeningEquiv : ∀ e : ℕ+,
      (functor (I.comap (K ^ (e : ℕ)).subschemeι)).IsEquivalence)
    (E : Scheme.CoherentFormalModules X I)
    (hApprox : ∃ H : RingedSpace.Coh X.toRingedSpace,
      ∃ alpha : E ⟶ (functor I).obj H,
        Scheme.CoherentFormalMap.StagesHaveUniformKernelCokernelAnnihilation K alpha) :
    (functor I).essImage E := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
