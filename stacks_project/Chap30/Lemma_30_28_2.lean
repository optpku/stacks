module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import stacks_project.Chap30.Lemma_30_28_1_AdicThickening

/-!
# Algebraization of a finite formal scheme over a proper first stage

A cartesian successor ladder of finite morphisms into the adic stages of a
separated finite type morphism over a complete Noetherian affine base, with
proper first stage over `S_1`, algebraizes to a finite morphism that is proper
over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Lemma 30.28.2: if `A` is Noetherian and `I`-adically complete, `f : X ⟶ Spec(A)` is
separated of finite type, and for `n ≥ 1` one is given schemes `Y n` with successor maps
over the adic stages `AdicThickening.stage f I n` forming cartesian squares, such that
each `Y n ⟶ X_n` is finite and `Y 1 ⟶ S_1` is proper, then there exists a finite morphism
`ι : W ⟶ X` with each `Y n` identified with the fibre product of `W` and `X_n` over `X`
via `IsPullback (π n) (toStage n) ι (AdicThickening.ι f I n)`. Pasting with
`isPullback_toAmbient_of_isPullback_ι` recovers the source identification
`Y n = W ×_S S_n`, i.e. `IsPullback (π n) (toStage n ≫ AdicThickening.toSpec f I n)
(ι ≫ f) (AdicThickening.toAmbient I n)`. Moreover `W` is proper over `S`. -/
@[stacks 09ZT]
theorem exists_algebraizingFinite
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [Scheme.Hom.FiniteType f]
    (Y : ℕ+ → Scheme.{u}) (succ : ∀ n, Y n ⟶ Y (n + 1))
    (toStage : ∀ n, Y n ⟶ AdicThickening.stage f I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition f I n))
    [∀ n, IsFinite (toStage n)]
    [IsProper (toStage 1 ≫ AdicThickening.toSpec f I 1)] :
    ∃ (W : Scheme.{u}) (ι : W ⟶ X) (π : ∀ n, Y n ⟶ W),
      IsFinite ι ∧ IsProper (ι ≫ f) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι f I n) :=
  sorry

end AlgebraicGeometry.Scheme
