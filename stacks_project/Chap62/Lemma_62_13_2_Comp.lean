/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Restriction

/-!
# Restriction of fibre-cycle families along an open of the total space

This file restricts a family of cycles on the fibres of `X / S` along an open
of `X`, keeping the base scheme `S`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/- Total-space restriction keeps the base scheme fixed. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.restrictOver :
  {X S : Scheme.{u}} → {f : X ⟶ S} → [LocallyOfFiniteType f] → {r : ℤ} →
    (α : CyclesOnFibers f r) → (U : X.Opens) → CyclesOnFibers (U.ι ≫ f) r)

/- Coefficients of a total-space restriction are the original fibre
coefficients along the identity-triangle fibre map. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.restrictOver_apply :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℤ} (α : CyclesOnFibers f r) (U : X.Opens)
    (s : S) (x : (U.ι ≫ f).fiber s),
    toAlgebraicCycle (restrictOver α U) s x =
      toAlgebraicCycle α s (idTriangleFiberMap U.ι rfl s x))

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
