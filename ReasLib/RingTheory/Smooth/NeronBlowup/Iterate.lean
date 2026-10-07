module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.NeronBlowup.Core

/-!
# Iterated affine Neron blowups

This file owns the deterministic sequence of affine Neron blowups and the
compatible transition maps from the initial factorization.
-/

@[expose] public section

noncomputable section

universe u v

namespace Algebra.DVR.Factorization

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L] [IsExtensionOfDiscreteValuationRings R L]
variable [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]

/-- Iterating the deterministic affine Neron blowup produces a sequence of
factorizations through the same target DVR. -/
@[stacks 0BJ6]
noncomputable def iteratedNeronBlowup
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    ℕ → Algebra.DVR.Factorization R L
  | 0 => S
  | n + 1 => (S.iteratedNeronBlowup π hπ n).neronBlowupStage π hπ

/-- The canonical map from the initial algebra to every iterated affine Neron blowup. -/
@[stacks 0BJ6]
noncomputable def toIteratedNeronBlowup
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    (n : ℕ) → S.mid →ₐ[R] (S.iteratedNeronBlowup π hπ n).mid
  | 0 => AlgHom.id R S.mid
  | n + 1 =>
      (NeronBlowup.fromSource (S.iteratedNeronBlowup π hπ n) π hπ).comp
        (S.toIteratedNeronBlowup π hπ n)

/-- Every iterated transition is compatible with the original map to the target DVR. -/
@[simp]
theorem toTarget_comp_toIterated
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) (n : ℕ) :
    (S.iteratedNeronBlowup π hπ n).toTarget.comp (S.toIteratedNeronBlowup π hπ n) =
      S.toTarget := sorry

end Algebra.DVR.Factorization
