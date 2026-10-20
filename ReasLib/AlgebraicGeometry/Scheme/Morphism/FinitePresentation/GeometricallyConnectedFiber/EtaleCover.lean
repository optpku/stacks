/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.GeometricallyConnectedFiber.EtaleNeighborhood

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyOfFinitePresentation

/-- A flat locally finitely presented morphism with geometrically reduced fibres admits an
étale cover whose members factor through étale base schemes by flat finitely presented
morphisms with geometrically connected and geometrically reduced fibres. -/
theorem exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [Flat f] [GeometricallyReduced f] :
    ∃ 𝒰 : X.Cover.{u} Scheme.etalePrecoverage, ∀ i : 𝒰.I₀,
      ∃ (Sᵢ : Scheme.{u}) (p : 𝒰.X i ⟶ Sᵢ) (q : Sᵢ ⟶ S)
        (h_etale : Etale q) (h_flat : Flat p)
        (h_finitePresentation : Scheme.Hom.FinitePresentation p)
        (h_connected : GeometricallyConnected p) (h_reduced : GeometricallyReduced p),
        p ≫ q = 𝒰.f i ≫ f := sorry

end AlgebraicGeometry.LocallyOfFinitePresentation
