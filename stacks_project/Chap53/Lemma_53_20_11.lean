module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPowerSeries.Basic
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SplitNode.Completion

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 53.20.11: a flat locally finite type morphism at a split node has the stated
completed local power-series presentation. -/
@[stacks 0CBX] #check
  (AlgebraicGeometry.Scheme.Hom.exists_completedStalk_powerSeries_quotient_of_splitNode :
    ∀ {T S : Scheme.{u}} (f : T ⟶ S) (t : T)
      [LocallyOfFiniteType f]
      [IsNoetherianRing (S.presheaf.stalk (f t))]
      (h_flat : f.flatAt t)
      (h_split :
        isSplitNodeAt (Over.mk (f.fiberToSpecResidueField (f t))) (f.asFiber t)),
      (let R := S.presheaf.stalk (f t)
       let Rhat := AdicCompletion (maximalIdeal R) R
       let B := T.presheaf.stalk t
       let Bhat := AdicCompletion (maximalIdeal B) B
       ∃ h : Rhat,
         h ∈ Ideal.map (algebraMap R Rhat) (maximalIdeal R) ∧
           ∃ e : Bhat ≃+*
               (MvPowerSeries (Fin 2) Rhat ⧸
                 Ideal.span
                   {((MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) -
                       MvPowerSeries.C h) : MvPowerSeries (Fin 2) Rhat)}),
             e.toRingHom.comp (AdicCompletion.mapLocal (f.stalkMap t).hom) =
               algebraMap Rhat
                 (MvPowerSeries (Fin 2) Rhat ⧸
                   Ideal.span
                     {((MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) -
                         MvPowerSeries.C h) : MvPowerSeries (Fin 2) Rhat)})))

end AlgebraicGeometry.Scheme.Hom
