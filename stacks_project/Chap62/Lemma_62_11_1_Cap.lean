/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Cap

/-!
# Action of fibre-cycle families on cycles

This file exposes the action of a family of `r`-cycles on the fibres of
`X / Y` on a cycle of `Y`, sending `Z_e(Y)` to `Z_{r + e}(X)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

variable {S X Y : Scheme.{u}} [UniversallyCatenary S]
    (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (r e : ℤ)

/- The fibre-cycle action sends degrees `r` and `e` to degree `r + e`. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.cap p f δ (r := r) (e := e) :
  CyclesOnFibers f r → CycleGroup Y (p.relativeDimensionFunction δ) e →
    CycleGroup X ((f ≫ p).relativeDimensionFunction δ) (r + e))

/- A fixed fibre-cycle family acts by an additive homomorphism in every degree. -/
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.capHom p f δ (r := r) :
  ∀ (α : CyclesOnFibers f r) (e : ℤ),
    CycleGroup Y (p.relativeDimensionFunction δ) e →+
      CycleGroup X ((f ≫ p).relativeDimensionFunction δ) (r + e))

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
