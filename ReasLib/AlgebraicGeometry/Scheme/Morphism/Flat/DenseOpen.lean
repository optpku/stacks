/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.DenseOpen

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsOpenImmersion

/-- A separated, locally finite-type, flat morphism that is an isomorphism over a
retrocompact scheme-theoretically dense open is an open immersion. -/
theorem of_isIso_restrict_of_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [Flat f] (U : S.Opens)
    [IsIso (f ∣_ U)] (hU_retrocompact : IsRetrocompact (U : Set S))
    (hU_dense : schemeTheoreticallyDense U) :
    IsOpenImmersion f := sorry

end AlgebraicGeometry.IsOpenImmersion
