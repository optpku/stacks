/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.StandardTame
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.RegularCartierExtension
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- A tame finite étale cover of the complement of a regular effective Cartier divisor is étale
locally a finite coproduct of standard root covers. -/
theorem exists_etaleLocal_sigma_standardTameCover
    {X D : Scheme.{u}} [IsLocallyNoetherian X] (i : D ⟶ X)
    [IsEffectiveCartierDivisor i] [Scheme.Regular D]
    (Y : FiniteEtale (closedImmersionComplement i).toScheme)
    (hY : IsTamelyRamifiedInCodimensionOne (closedImmersionComplement i)
      (dense_closedImmersionComplement i) Y) :
    ∀ x : X, ∃ U : Scheme.EtaleNeighborhood X x, ∃ (A : Type u) (_ : CommRing A)
      (_ : IsNoetherianRing A),
      ∃ eU : U.toEtale.left ≅ Spec (CommRingCat.of A),
        ∃ f : A, f ∈ nonZeroDivisors A ∧ _root_.IsReduced (A ⧸ Ideal.span {f}) ∧
        ∃ n : ℕ, ∃ e : Fin n → ℕ,
          ∃ he : ∀ j, 1 ≤ e j ∧ IsUnit (e j : A),
            ∃ φ : Spec (CommRingCat.of (Localization.Away f)) ⟶
                (closedImmersionComplement i).toScheme,
              IsPullback φ
                (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫ eU.inv)
                (closedImmersionComplement i).ι U.toEtale.hom ∧
                Nonempty ((finiteEtaleBaseChange φ).obj Y ≅
                  sigmaStandardTameCoverAway f e he) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
