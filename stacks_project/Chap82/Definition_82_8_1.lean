/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.IntegralImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
import StacksCheckRecall

/-!
# Proper pushforward of cycles

In Situation 82.2.1, a proper morphism of good algebraic spaces over `B`
pushes `k`-cycles forward by the residue-weighted integral-image formula on
generators, extended linearly as `Hom.properPushforwardHom`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

section

variable {S : Scheme.{u}} {B X Y : AlgebraicSpace S}
  [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ Y) [Proper f] (hf : f ≫ pY = pX) (k : ℤ)

section

variable [IsDecent Y] (Z : ClosedSubspace X) [IsIntegral Z.X]
variable (hZ : closedSubspaceDeltaDimension pX δ Z = (k : EInt))

open scoped Classical in
/- Definition 82.8.1 (1): For an integral closed subspace `Z` of `δ`-dimension
`k`, proper pushforward sends `[Z]` to zero when its integral image has smaller
dimension, and otherwise to the finite generic degree times the image cycle.
The dimension bound ensures that the latter branch has dimension `k`. -/
@[stacks 0EP1] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardCycle_integralClosedSubspace
    pX pY δ f hf k Z hZ :
    let ξ := Points.map Z.ι (ClosedSubspace.integralGenericPoint Z)
    properPushforwardCycle pX pY δ f hf
        (locallyFinsuppWithin.single ξ 1) =
      if AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension pY δ (Z.integralImage f) < (k : EInt) then
        0
      else
        (residueDegreeAlong pX pY f ξ : ℤ) •
          locallyFinsuppWithin.single
            (Points.map (Z.ι ≫ f) (ClosedSubspace.integralGenericPoint Z)) 1)

end

/- Definition 82.8.1 (2): The pushforward of a `k`-cycle `α = ∑ n_Z [Z]` is
the locally finite sum `f_* α = ∑ n_Z f_*[Z]`, encoded by the additive map
on `k`-cycles. Local finiteness is supplied by Lemma 82.7.5. -/
@[stacks 0EP1] #check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardHom pX pY δ f hf k :
  cycleGroup pX δ k →+ cycleGroup pY δ k)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardCycle_apply pX pY δ f hf :
  ∀ (α : Function.locallyFinsupp (Points X) ℤ) (y : Points Y),
    properPushforwardCycle pX pY δ f hf α y =
      ∑ᶠ x ∈ Points.map f ⁻¹' {y}, (mapCoeff pX pY δ f x : ℤ) * α x)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.properPushforwardHom_apply pX pY δ f hf k :
  ∀ (α : cycleGroup pX δ k),
    (properPushforwardHom pX pY δ f hf k α).val =
      properPushforwardCycle pX pY δ f hf α)

end

end AlgebraicGeometry.AlgebraicSpace.Hom
