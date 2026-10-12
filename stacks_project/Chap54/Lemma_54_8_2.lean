/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroLocusCokernel
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 54.8.2: for a local normal Nagata domain of dimension two and a nonzero element `a`,
the cokernels of constants into zero-locus global sections on normal modifications have
a uniform finite-length bound. -/
@[stacks 0AXJ] #check (AlgebraicGeometry.Scheme.Hom.exists_zeroLocusCokernel_length_bound :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [_root_.IsNormalRing A],
    ringKrullDim A = 2 → ∀ (a : A), a ≠ 0 →
    ∃ N : ℕ, ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f],
      X.isNormal → Module.length A (Scheme.Hom.zeroLocusCokernel f a) ≤ (N : ℕ∞))
