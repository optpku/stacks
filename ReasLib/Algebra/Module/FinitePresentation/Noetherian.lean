/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.Algebra.Module.FinitePresentation.Exact

@[expose] public section

universe u v

namespace Module

/-- For a module over a Noetherian local ring, Noetherianity, finite generation, and
the existence of a finite free presentation are equivalent. -/
theorem noetherianFinitePresentation_tfae
    (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] :
    List.TFAE
      [ IsNoetherian R M
      , Module.Finite R M
      , ∃ n m : ℕ, ∃ f : (Fin m → R) →ₗ[R] (Fin n → R),
          ∃ g : (Fin n → R) →ₗ[R] M, Function.Exact f g ∧ Function.Surjective g
      ] := sorry

end Module
