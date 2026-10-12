/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Kummer
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The additive Kummer short complex is short exact on the small étale site when `n` is a unit on `S`. -/
theorem kummerSmallEtaleShortExact
    (S : Scheme.{u}) (n : ℕ)
    (h_n : IsUnit (n : Γ(S, ⊤))) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (smallCommStructureSheaf .etale S) n).ShortExact := sorry

/-- The additive Kummer short complex is short exact on the big étale site when `n` is a unit on `S`. -/
theorem kummerBigEtaleShortExact
    (S : Scheme.{u}) (n : ℕ)
    (h_n : IsUnit (n : Γ(S, ⊤))) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .etale S) n).ShortExact := sorry

end AlgebraicGeometry.Scheme

/-- For a positive natural number invertible on a scheme, the small-étale Kummer sequence is short exact. -/
theorem kummerSequence_smallEtale_shortExact
    (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n)
    (h_n : IsUnit (n : Γ(S, ⊤))) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (smallCommStructureSheaf .etale S) n).ShortExact := sorry

/-- For a positive natural number invertible on a scheme, the big-étale Kummer sequence is short exact. -/
theorem kummerSequence_bigEtale_shortExact
    (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n)
    (h_n : IsUnit (n : Γ(S, ⊤))) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .etale S) n).ShortExact := sorry

end
