/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.OverField.SplitNode
public import ReasLib.RingTheory.AdicCompletion.LocalMap

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A flat locally finite type morphism at a split node has a completed local ring
presented by two formal parameters with product equal to an element of the completed
maximal ideal of the base stalk. -/
theorem exists_completedStalk_powerSeries_quotient_of_splitNode
    {T S : Scheme.{u}} (f : T ⟶ S) (t : T)
    [LocallyOfFiniteType f]
    [IsNoetherianRing (S.presheaf.stalk (f t))]
    (h_flat : f.flatAt t)
    (h_split :
      isSplitNodeAt (Over.mk (f.fiberToSpecResidueField (f t))) (f.asFiber t)) :
    let R := S.presheaf.stalk (f t)
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
                      MvPowerSeries.C h) : MvPowerSeries (Fin 2) Rhat)}) := sorry

end AlgebraicGeometry.Scheme.Hom
