/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.AdicThickening

/-!
# Algebraization of formal closed subschemes

Cartesian adic ladders with closed first stage proper over the quotient base
algebraize inside a separated finite type scheme over a complete Noetherian ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Over an adically complete Noetherian ring, a cartesian ladder over the adic stages
of a separated finite type scheme, with closed first stage proper over the first
quotient base, is induced by a closed subscheme proper over the original base. -/
theorem exists_algebraizingClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : ℕ+ → Scheme.{u}) (succ : ∀ n, Z n ⟶ Z (n + 1))
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage f I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition f I n))
    [IsClosedImmersion (toStage 1)]
    [IsProper (toStage 1 ≫ AdicThickening.toSpec f I 1)] :
    ∃ (W : Scheme.{u}) (ι : W ⟶ X) (π : ∀ n, Z n ⟶ W),
      IsClosedImmersion ι ∧ IsProper (ι ≫ f) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι f I n) :=
  sorry

end AlgebraicGeometry.Scheme
