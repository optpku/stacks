module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Data.PNat.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AdicThickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Algebraization of finite formal algebraic spaces

A cartesian ladder over the adic stages of a separated finite type algebraic space
over a complete Noetherian affine base, with finite first stage proper over the
first quotient base, algebraizes to a finite morphism proper over the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Over an adically complete Noetherian ring, a cartesian ladder over the adic stages
of a separated finite type algebraic space, with finite first stage proper over the first
quotient base, is induced by a finite morphism proper over the original base. -/
theorem exists_algebraizingFinite
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) [Separated (toBase X)] [FiniteType (toBase X)]
    (Y : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A))) (succ : ∀ n, Y n ⟶ Y (n + 1))
    (toStage : ∀ n, Y n ⟶ AdicThickening.stage X I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition X I n))
    [IsFinite (toStage 1)]
    [Proper (toStage 1 ≫ AdicThickening.toSpec X I 1)] :
    ∃ (W : AlgebraicSpace (Spec (CommRingCat.of A))) (ι : W ⟶ X) (π : ∀ n, Y n ⟶ W),
      IsFinite ι ∧ Proper (ι ≫ toBase X) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
