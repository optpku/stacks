/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.Tor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change-of-rings Tor spectral sequence

For a ring map `R ⟶ S`, an `R`-module `M`, and an `S`-module `N`, this leaf records the
spectral sequence
`Tor_n^S(Tor_m^R(M,S),N) ⟹ Tor_(m+n)^R(M,N)` in `ModuleCat S`.

@stack 068F
-/

@[expose] public section

open CategoryTheory
open scoped DerivedTensorChangeOfRings DerivedTensorWithAlgebra

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

local notation "ModR" => ModuleCat R
local notation "ModS" => ModuleCat S
local notation "HS" => DerivedCategory.homologyFunctor ModS
local notation "singleR" => DerivedCategory.singleFunctor ModR (0 : ℤ)
local notation "singleS" => DerivedCategory.singleFunctor ModS (0 : ℤ)

/-- The page-two term `Tor_n^S(Tor_m^R(M,S),N)`, with its natural `S`-module structure. -/
@[stacks 068F "change-of-rings Tor page two"]
abbrev pageTwo (M : ModR) (N : ModS) (m n : ℕ) : ModS :=
  ((Tor ModS n).obj
      ((HS (-(m : ℤ))).obj ((singleR).obj M ⊗[R]^L[S]))).obj N

/-- The abutment term `Tor_k^R(M,N)`, with the `S`-module structure induced by `N`. -/
@[stacks 068F "change-of-rings Tor abutment"]
abbrev abutment (M : ModR) (N : ModS) (k : ℕ) : ModS :=
  (HS (-(k : ℤ))).obj
    ((singleR).obj M ⊗[R]^L[S] (singleS).obj N)

/-- Convergence to change-of-rings Tor means convergence from a filtered complex whose
cohomology identifies with the displayed `S`-module abutment. -/
@[stacks 068F "change-of-rings Tor convergence"]
def ConvergesTo
    (E : CohomologicalSpectralSequence ModS 0) (M : ModR) (N : ModS) : Prop :=
  ∃ F : FilteredComplex ModS,
    FilteredComplex.Cohomology.Convergence.Converges F E ∧
      ∀ k : ℕ, Nonempty (F.underlying.homology (-(k : ℤ)) ≅ abutment R S M N k)

namespace ConvergesTo

/-- The filtered-complex specification of convergence to change-of-rings Tor. -/
@[stacks 068F "change-of-rings Tor convergence specification"]
theorem spec
    {E : CohomologicalSpectralSequence ModS 0} {M : ModR} {N : ModS} :
    ConvergesTo R S E M N ↔
      ∃ F : FilteredComplex ModS,
        FilteredComplex.Cohomology.Convergence.Converges F E ∧
          ∀ k : ℕ, Nonempty (F.underlying.homology (-(k : ℤ)) ≅ abutment R S M N k) := sorry

end ConvergesTo

/-- A change-of-rings Tor spectral sequence has page two
`Tor_n^S(Tor_m^R(M,S),N)` and converges to `Tor_*^R(M,N)` in `ModuleCat S`. -/
@[stacks 068F "change-of-rings Tor spectral sequence"]
def IsChangeOfRings
    (E : CohomologicalSpectralSequence ModS 0) (M : ModR) (N : ModS) : Prop :=
  (∀ m n : ℕ,
      Nonempty ((E.page 2).X (-(n : ℤ), -(m : ℤ)) ≅ pageTwo R S M N m n)) ∧
    ConvergesTo R S E M N

namespace IsChangeOfRings

/-- The page-two and convergence clauses of a change-of-rings Tor spectral sequence. -/
@[stacks 068F "change-of-rings Tor spectral sequence specification"]
theorem spec
    {E : CohomologicalSpectralSequence ModS 0} {M : ModR} {N : ModS} :
    IsChangeOfRings R S E M N ↔
      (∀ m n : ℕ,
          Nonempty ((E.page 2).X (-(n : ℤ), -(m : ℤ)) ≅ pageTwo R S M N m n)) ∧
        ConvergesTo R S E M N := sorry

/-- The page-two entries have the source-prescribed iterated Tor identification. -/
@[stacks 068F "change-of-rings Tor page-two identification"]
theorem pageTwoIso
    {E : CohomologicalSpectralSequence ModS 0} {M : ModR} {N : ModS}
    (h : IsChangeOfRings R S E M N) (m n : ℕ) :
    Nonempty ((E.page 2).X (-(n : ℤ), -(m : ℤ)) ≅ pageTwo R S M N m n) := sorry

/-- A change-of-rings Tor spectral sequence converges to the displayed abutment. -/
@[stacks 068F "change-of-rings Tor convergence consequence"]
theorem converges
    {E : CohomologicalSpectralSequence ModS 0} {M : ModR} {N : ModS}
    (h : IsChangeOfRings R S E M N) : ConvergesTo R S E M N := sorry

end IsChangeOfRings

/-- Example 15.62.2: for `R ⟶ S`, an `R`-module `M`, and an `S`-module `N`, there is a
spectral sequence `Tor_n^S(Tor_m^R(M,S),N) ⟹ Tor_(m+n)^R(M,N)`. -/
@[stacks 068F]
theorem existsChangeOfRings (M : ModR) (N : ModS) :
    ∃ E : CohomologicalSpectralSequence ModS 0, IsChangeOfRings R S E M N := sorry

end CategoryTheory.DerivedCategory.TorSpectralSequence.ChangeOfRings
