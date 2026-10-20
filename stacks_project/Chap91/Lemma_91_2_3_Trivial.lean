module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import ReasLib.RingTheory.RingHom.SquareZero.Split

/-!
# Split square-zero solution of the identity algebra-extension diagram

The identity diagram 0 ⟶ 0 ⟶ A ⟶ A ⟶ 0 with zero kernel map 0 ⟶ N admits the
split solution whose middle ring is `TrivSqZeroExt B N`, i.e. the source's N ⊕ B.
-/

@[expose] public section

noncomputable section

universe u

namespace RingHom.SquareZeroExtension

/-- The source compatibility name for the canonical trivial-extension projection. -/
def trivFstRingHom (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]
    [Module Bᵐᵒᵖ N] [IsCentralScalar B N] :
    TrivSqZeroExt B N →+* B :=
  (TrivSqZeroExt.fstHom B B N).toRingHom

#check (trivialSolution : ∀ (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N],
  Solution (B := B) (N := N) (RingHom.id A) (zeroKernelMap A B N))

end SquareZeroExtension

end RingHom
