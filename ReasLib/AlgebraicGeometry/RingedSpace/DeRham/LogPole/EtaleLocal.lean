/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined

/-- If `S` is locally Noetherian, `f : X ⟶ S` is locally of finite type, and `i : Y ⟶ X` is
an effective Cartier divisor, and every point of `Y` admits an étale chart `φ : U ⟶ X` over
`S` such that the restriction of `ψ : U ⟶ V` to the inverse-image divisor is étale, then the
relative de Rham complex with logarithmic poles along `Y` is defined. -/
theorem ofEtaleLocal
    {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsEffectiveCartierDivisor i]
    (h_chart : ∀ y : Y,
      ∃ (U V : Scheme.{u}) (φ : U ⟶ X) (ψ : U ⟶ V) (g : V ⟶ S) (u : U),
        Etale φ ∧ φ ≫ f = ψ ≫ g ∧ φ u = i y ∧
          Etale (pullback.fst φ i ≫ ψ)) :
    IsDefined f i := sorry

end AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined
