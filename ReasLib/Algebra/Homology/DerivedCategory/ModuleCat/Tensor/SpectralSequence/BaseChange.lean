module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence.Tor
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor spectral sequence for a flat base-change square

This leaf records the change-of-rings Tor spectral sequence for `B' = B ⊗[A] A'`.  Its page-two
terms are displayed after restriction along the canonical right inclusion `A' ⟶ B'`, while the
abutment retains its canonical `B'`-module structure.

@stack 0620
-/

@[expose] public section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange

variable (A A' : Type u) [CommRing A] [CommRing A']
variable {B : Type u} [CommRing B] [Algebra A B] [Algebra A A']

local notation "ModA'" => ModuleCat A'
local notation "ModB" => ModuleCat B
local notation "BaseChangedRing" => TensorProduct A B A'
local notation "ModBaseChanged" => ModuleCat BaseChangedRing
local notation "HA'" => DerivedCategory.homologyFunctor ModA'
local notation "singleB" => DerivedCategory.singleFunctor ModB (0 : ℤ)

/-- The page-two term `Tor_i^A(Tor_j^B(M,N),A')`, regarded as an `A'`-module. -/
@[stacks 0620 "base-change Tor page two"]
abbrev pageTwo (M N : ModB) (i j : ℕ) : ModA' :=
  (HA' (-(i : ℤ))).obj
    (((ModuleCat.derivedRestrictionOfScalars (algebraMap A B)).obj
      ((singleB).obj (((Tor ModB j).obj M).obj N))) ⊗[A]^L[A'])

/-- The abutment term `Tor_n^(B ⊗[A] A')(M ⊗[A] A',N ⊗[A] A')`. -/
@[stacks 0620 "base-change Tor abutment"]
abbrev abutment (M N : ModB) (n : ℕ) : ModBaseChanged :=
  ((Tor ModBaseChanged n).obj
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] BaseChangedRing)).obj M)).obj
    ((ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] BaseChangedRing)).obj N)

/-- Convergence to base-changed Tor means convergence from a filtered complex whose underlying
cohomology identifies with the displayed Tor abutment. -/
@[stacks 0620 "base-change Tor convergence"]
def ConvergesTo
    (E : CohomologicalSpectralSequence ModBaseChanged 0) (M N : ModB) : Prop :=
  ∃ F : FilteredComplex ModBaseChanged,
    FilteredComplex.Cohomology.Convergence.Converges F E ∧
      ∀ n : ℕ, Nonempty (F.underlying.homology (-(n : ℤ)) ≅ abutment A A' M N n)

namespace ConvergesTo

/-- The filtered-complex specification of convergence to base-changed Tor. -/
@[stacks 0620 "base-change Tor convergence specification"]
theorem spec
    {E : CohomologicalSpectralSequence ModBaseChanged 0} {M N : ModB} :
    ConvergesTo A A' E M N ↔
      ∃ F : FilteredComplex ModBaseChanged,
        FilteredComplex.Cohomology.Convergence.Converges F E ∧
          ∀ n : ℕ, Nonempty (F.underlying.homology (-(n : ℤ)) ≅ abutment A A' M N n) := sorry

end ConvergesTo

/-- A Tor base-change spectral sequence has page two `Tor_i^A(Tor_j^B(M,N),A')` after
restriction along `A' ⟶ B ⊗[A] A'`, and converges to Tor over `B ⊗[A] A'`. -/
@[stacks 0620 "base-change Tor spectral sequence"]
def IsBaseChange
    (E : CohomologicalSpectralSequence ModBaseChanged 0) (M N : ModB) : Prop :=
  (∀ i j : ℕ,
      Nonempty
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight : A' →ₐ[A] BaseChangedRing)).obj
              ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅ pageTwo A A' M N i j)) ∧
    ConvergesTo A A' E M N

namespace IsBaseChange

/-- The page-two and convergence clauses of a Tor base-change spectral sequence. -/
@[stacks 0620 "base-change Tor spectral sequence specification"]
theorem spec
    {E : CohomologicalSpectralSequence ModBaseChanged 0} {M N : ModB} :
    IsBaseChange A A' E M N ↔
      (∀ i j : ℕ,
          Nonempty
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight : A' →ₐ[A] BaseChangedRing)).obj
                  ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅ pageTwo A A' M N i j)) ∧
        ConvergesTo A A' E M N := sorry

/-- The page-two entries have the source-prescribed Tor identification over `A'`. -/
@[stacks 0620 "base-change Tor page-two identification"]
theorem pageTwoIso
    {E : CohomologicalSpectralSequence ModBaseChanged 0} {M N : ModB}
    (h : IsBaseChange A A' E M N) (i j : ℕ) :
    Nonempty
      ((ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight : A' →ₐ[A] BaseChangedRing)).obj
            ((E.page 2).X (-(i : ℤ), -(j : ℤ))) ≅ pageTwo A A' M N i j) := sorry

/-- A Tor base-change spectral sequence converges to the displayed base-changed Tor abutment. -/
@[stacks 0620 "base-change Tor convergence consequence"]
theorem converges
    {E : CohomologicalSpectralSequence ModBaseChanged 0} {M N : ModB}
    (h : IsBaseChange A A' E M N) : ConvergesTo A A' E M N := sorry

end IsBaseChange

/-- Example 15.62.3: if `B`, `M`, and `N` are flat over `A`, there is a spectral sequence
`Tor_i^A(Tor_j^B(M,N),A') ⟹ Tor_(i+j)^(B ⊗[A] A')(M',N')`. -/
@[stacks 0620]
theorem existsBaseChange
    (M N : ModB) (hB : Module.Flat A B)
    (hM : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj M))
    (hN : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A B)).obj N)) :
    ∃ E : CohomologicalSpectralSequence ModBaseChanged 0, IsBaseChange A A' E M N := sorry

end CategoryTheory.DerivedCategory.TorSpectralSequence.BaseChange
