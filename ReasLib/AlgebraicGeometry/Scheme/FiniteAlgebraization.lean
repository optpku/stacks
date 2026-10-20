module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Algebraization of finite formal schemes

Finite morphisms on a compatible adic tower with proper first stage algebraize
to a finite morphism whose source is proper over the complete Noetherian base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A compatible finite tower over the adic thickenings of a separated finite-type scheme over a
complete Noetherian affine base admits a finite algebraization that is proper over the base and
recovers every stage compatibly. -/
theorem exists_algebraizingFinite
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Y : ℕ+ → Scheme.{u}) (successor : ∀ n, Y n ⟶ Y (n + 1))
    (toX : ∀ n, Y n ⟶ X)
    (toBase : ∀ n, Y n ⟶ Spec (CommRingCat.of (A ⧸ I ^ (n : ℕ))))
    (h_over : ∀ n, toX n ≫ f =
      toBase n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n : ℕ)))))
    (h_transition : ∀ n, successor n ≫ toX (n + 1) = toX n)
    (h_cartesian : ∀ n, IsPullback (successor n) (toBase n)
      (toBase (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I (n : ℕ)))))
    (h_finite : ∀ n, IsFinite (pullback.lift (toX n) (toBase n) (h_over n)))
    (h_proper : IsProper (toBase 1)) :
    ∃ (W : Scheme.{u}) (inclusion : W ⟶ X) (comparison : ∀ n, Y n ⟶ W),
      IsFinite inclusion ∧ IsProper (inclusion ≫ f) ∧
        (∀ n, comparison n ≫ inclusion = toX n) ∧
        (∀ n, successor n ≫ comparison (n + 1) = comparison n) ∧
        (∀ n, IsPullback (comparison n) (toBase n) (inclusion ≫ f)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n : ℕ)))))) := sorry

end AlgebraicGeometry.Scheme
