/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Square
public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAtAmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.Existence

/-!
# Existence of complete dévissages after elementary étale refinement
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module on a locally finite-type scheme morphism admits a
complete dévissage after a pointed elementary étale refinement at an ambient point where
the local fibre-support dimension is a natural number.

As in the one-step existence theorem, the dimension hypothesis excludes empty local fibre
support, whose dimension is `⊥`. Stacks Tag 05HR omits this boundary in its statement, but
its proof inducts on the local fibre-support dimension as an integer. The complete
dévissages used here have a nonempty chain with a generic point in the initial model fibre. -/
theorem exists_completeDevissageAtAmbientPoint {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [h_quasicoherent : F.IsQuasicoherent]
    [h_finiteType : F.IsFiniteType] (x : X)
    (h_dim : ∃ n : ℕ, ambientFiberSupportDimensionAt f F x = (n : WithBot ℕ∞)) :
    ∃ square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare f x,
      let F' := (Scheme.Modules.pullback square.source.obj.toEtale.hom).obj F
      let h_quasicoherent' : F'.IsQuasicoherent :=
        @pullback_isQuasicoherent _ _ square.source.obj.toEtale.hom F h_quasicoherent
      let h_finiteType' : F'.IsFiniteType :=
        @pullback_isFiniteType _ _ square.source.obj.toEtale.hom F h_finiteType
      ∃ h_refined : LocallyOfFiniteType square.map,
        Nonempty (@CompleteDevissageAtAmbientPoint _ _ square.map F' h_refined
          h_quasicoherent' h_finiteType' square.source.obj.point) := sorry

end AlgebraicGeometry.Scheme.Modules
