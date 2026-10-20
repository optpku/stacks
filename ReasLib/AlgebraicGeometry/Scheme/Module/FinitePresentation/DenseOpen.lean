/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.FlatOverAt
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Retrocompact

/-!
# Extending finite presentation from a dense open

Finite presentation of a scheme module can be extended from the inverse image of a
retrocompact scheme-theoretically dense open under suitable flatness and finiteness hypotheses.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFinitePresentation

/-- A finite-type quasicoherent module flat over a locally finitely presented morphism is
finitely presented if its restriction above a retrocompact scheme-theoretically dense open of
the base is finitely presented. -/
@[stacks 081N]
theorem of_restrict_of_flatOver
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_flat : flatOver F f) (U : S.Opens)
    (hU_retrocompact : IsRetrocompact (U : Set S))
    (hU_dense : schemeTheoreticallyDense U)
    (hF_U : (F.restrict ((f ⁻¹ᵁ U).ι)).IsFinitePresentation) :
    F.IsFinitePresentation := sorry

end AlgebraicGeometry.Scheme.Modules.IsFinitePresentation
