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

/-- The Kummer short complex is short exact on the big syntomic site of a scheme
when the exponent is a positive natural number. -/
theorem kummerBigSyntomicShortExact
    (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .syntomic S) n).ShortExact := sorry

/-- The Kummer short complex is short exact on the big fppf site of a scheme
when the exponent is a positive natural number. -/
theorem kummerBigFppfShortExact
    (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .fppf S) n).ShortExact := sorry

/-- The Kummer short complex can fail to be short exact on the big Zariski site
even when the exponent is positive and invertible on the base scheme. -/
theorem kummerBigZariskiNotShortExact :
    ∃ (S : Scheme.{u}) (n : ℕ),
      0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧
        ¬ (CategoryTheory.Sheaf.kummerAddShortComplex
          (bigCommStructureSheaf .zariski S) n).ShortExact := sorry

/-- The Kummer short complex is short exact on the big smooth site of a scheme
when the exponent is invertible on the base scheme. -/
theorem kummerBigSmoothShortExact
    (S : Scheme.{u}) (n : ℕ) (h_n : IsUnit (n : Γ(S, ⊤))) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .smooth S) n).ShortExact := sorry

/-- The Kummer short complex is not short exact for every positive exponent on
the big smooth site of schemes. -/
theorem kummerBigSmoothNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .smooth S) n).ShortExact := sorry

/-- The Kummer short complex is not short exact for every positive exponent on
the big étale site of schemes. -/
theorem kummerBigEtaleNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .etale S) n).ShortExact := sorry

/-- The Kummer short complex is not short exact for every positive exponent on
the big Zariski site of schemes. -/
theorem kummerBigZariskiNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .zariski S) n).ShortExact := sorry

end AlgebraicGeometry.Scheme

end
