/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Characteristic-zero liftability of schemes over fields

This file records the existence predicate for finite-type flat characteristic-zero
models of schemes over fields and the corresponding finite-field counterexample.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A scheme over a field lifts to characteristic zero when it is isomorphic to
the base change of a finite-type flat scheme over the spectrum of a
characteristic-zero domain. -/
def liftsToCharZero {k : Type u} [Field k] (X : SchemeOverField k) : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : CharZero R)
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of R)) (_ : Flat f)
      (_ : Scheme.Hom.FiniteType f) (φ : R →+* k),
    Nonempty (X ≅ Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom φ))))

/-- The characteristic-zero liftability predicate is equivalent to its explicit
finite-type flat model specification. -/
theorem liftsToCharZero_iff {k : Type u} [Field k] (X : SchemeOverField k) :
    liftsToCharZero X ↔
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : CharZero R)
          (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of R)) (_ : Flat f)
          (_ : Scheme.Hom.FiniteType f) (φ : R →+* k),
        Nonempty (X ≅ Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))) := sorry

/-- Some finite-type scheme over a finite field does not lift to characteristic
zero in the sense of `liftsToCharZero`. -/
theorem exists_finiteType_not_liftsToCharZero :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (X : SchemeOverField k)
      (_ : Scheme.Hom.FiniteType X.hom),
      ¬ liftsToCharZero X := sorry

end AlgebraicGeometry.SchemeOverField
