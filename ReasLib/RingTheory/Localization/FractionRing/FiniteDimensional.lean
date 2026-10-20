/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Localization.AsSubring
public import ReasLib.RingTheory.Localization.FractionRing.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-dimensional transport across fraction rings

This leaf owns the generic transport from a finite-dimensional field extension `K ⊆ L` to the
fraction ring of an intermediate `R`-subalgebra of `K`.  The canonical fraction-ring algebra and
its scalar tower are bound inside the statement, so consumers do not need a chapter-local
`FractionRing.liftAlgebra` instance.
-/

@[expose] public section

universe u v w

namespace Subalgebra

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- The finite-dimensionality of `K ⊆ L` transports to the fraction ring of every intermediate
`R`-subalgebra of `K`.  The `letI` bindings select the canonical fraction-ring action on `L`; they
are part of the owner statement rather than ambient chapter infrastructure. -/
@[stacks 00PH "finite-dimensional transport to an intermediate fraction ring"]
theorem finiteDimensional_fractionRing
    (A : Subalgebra R K) [FiniteDimensional K L] :
    letI : FaithfulSMul A L :=
      FaithfulSMul.of_field_isFractionRing (R := A) (S := L) (K := K) (L := L)
    letI : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    letI : IsScalarTower A (FractionRing A) L :=
      FractionRing.isScalarTower_liftAlgebra A L
    FiniteDimensional (FractionRing A) L := sorry

end Subalgebra
