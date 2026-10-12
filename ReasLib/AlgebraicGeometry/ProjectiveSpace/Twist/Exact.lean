/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.LocallyFree
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Exact complexes of twisting sheaves on projective space

This file records the existence of the exact complex of twisting sheaves on standard projective
space over a commutative ring.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- For every integer `a`, standard projective `n`-space over `A` admits an exact cochain complex
of finite locally free module sheaves, supported in degrees `0` through `n + 1`, whose degree-`i`
term is the coproduct of `Nat.choose (n + 1) i` copies of `twistingSheaf A n (a + i)`. -/
@[stacks 0BQS]
theorem existsExactTwistingSheafComplex
    (A : Type u) [CommRing A] (n : ℕ) (a : ℤ) :
    ∃ K : CochainComplex (scheme A n).Modules ℤ,
      K.Acyclic ∧
        K.IsStrictlyGE 0 ∧
        K.IsStrictlyLE (Int.ofNat (n + 1)) ∧
        SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree K ∧
        ∀ i : ℕ, i ≤ n + 1 →
          Nonempty
            (K.X (Int.ofNat i) ≅
              ∐ fun _ : Fin (Nat.choose (n + 1) i) ↦
                twistingSheaf A n (a + Int.ofNat i)) := sorry

end AlgebraicGeometry.ProjectiveSpace
