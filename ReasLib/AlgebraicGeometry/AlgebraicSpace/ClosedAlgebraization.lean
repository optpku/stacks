module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AdicThickening

/-!
# Algebraization of a formal closed subspace

A cartesian successor ladder of closed immersions into the adic stages of a
separated finite type morphism of algebraic spaces over a complete Noetherian
affine base algebraizes to a closed immersion that is proper over the base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Over an adically complete Noetherian ring, a cartesian ladder over the adic stages
of a separated finite type algebraic space, with closed first stage proper over the first
quotient base, is induced by a closed subspace proper over the original base. -/
theorem exists_algebraizingClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Separated (toBase X)]
    [FiniteType (toBase X)] (Z : ℕ+ → AlgebraicSpace (Spec (CommRingCat.of A)))
    (succ : ∀ n, Z n ⟶ Z (n + 1))
    (toStage : ∀ n, Z n ⟶ AdicThickening.stage X I n)
    (h_pb : ∀ n, IsPullback (succ n) (toStage n) (toStage (n + 1))
      (AdicThickening.transition X I n))
    [IsClosedImmersion (toStage 1)]
    [Proper (toStage 1 ≫ AdicThickening.toSpec X I 1)] :
    ∃ (W : AlgebraicSpace (Spec (CommRingCat.of A))) (ι : W ⟶ X)
      (π : ∀ n, Z n ⟶ W),
      IsClosedImmersion ι ∧ Proper (ι ≫ toBase X) ∧
        ∀ n, IsPullback (π n) (toStage n) ι (AdicThickening.ι X I n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
