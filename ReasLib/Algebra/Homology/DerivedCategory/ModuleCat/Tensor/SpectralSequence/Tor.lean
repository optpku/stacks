/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.SpectralSequence
public import ReasLib.CategoryTheory.Homology.ChainShift
public import ReasLib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor spectral sequences for a bounded-below chain complex

This leaf records the two Tor spectral sequences obtained by tensoring a bounded-below chain
complex with a module.  It uses homological indexing on the public page formulas while retaining
the canonical cohomological spectral-sequence owner underneath.

@stack 061Z
-/

@[expose] public section

open CategoryTheory
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.TorSpectralSequence

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "H" => DerivedCategory.homologyFunctor ModR
local notation "single₀" => DerivedCategory.singleFunctor ModR (0 : ℤ)

/-- The cochain view of a homologically indexed chain complex. -/
@[stacks 061Z "cochain view used by the Tor spectral sequences"]
abbrev cochainView (K : ChainComplex ModR ℤ) : CochainComplex ModR ℤ :=
  (ChainComplex.chainToCochain ModR).obj K

/-- A chain complex is bounded below when its cochain view vanishes in sufficiently positive
degrees. -/
@[stacks 061Z "bounded-below condition for the Tor spectral sequences"]
def IsBoundedBelow (K : ChainComplex ModR ℤ) : Prop :=
  ∃ n : ℤ, (cochainView K).IsStrictlyLE n

namespace IsBoundedBelow

/-- The source-semantic specification of boundedness below. -/
theorem spec {K : ChainComplex ModR ℤ} :
    IsBoundedBelow K ↔ ∃ n : ℤ, (cochainView K).IsStrictlyLE n := Iff.rfl

end IsBoundedBelow

/-- The common abutment entry `H_n(K ⊗[R]^L M)` of the two Tor spectral sequences. -/
@[stacks 061Z "Tor spectral-sequence abutment"]
abbrev abutment (K : ChainComplex ModR ℤ) (M : ModR) (n : ℤ) : ModR :=
  (H (-n)).obj
    (DerivedCategory.Q.obj (cochainView K) ⊗[R]^L (single₀).obj M)

/-- The first spectral sequence's homologically indexed page-two entry
`Tor_j^R(H_i(K), M)`. -/
@[stacks 061Z "page-two term of the homology-first Tor spectral sequence"]
abbrev firstPageTwo (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) : ModR :=
  ((Tor ModR j).obj (K.homology i)).obj M

/-- The cohomological page-two entry corresponding to homological bidegree `(i,j)`. -/
@[stacks 061Z "cohomologically indexed page-two Tor term"]
abbrev firstPageTwoObject
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) : ModR :=
  (E.page 2).X (-(j : ℤ), -i)

/-- The second spectral sequence's homologically indexed page-one entry `Tor_j^R(K_i, M)`. -/
@[stacks 061Z "page-one term of the terms-first Tor spectral sequence"]
abbrev secondPageOne (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) : ModR :=
  ((Tor ModR j).obj (K.X i)).obj M

/-- The cohomological page-one entry corresponding to homological bidegree `(i,j)`. -/
@[stacks 061Z "cohomologically indexed page-one Tor term"]
abbrev secondPageOneObject
    (E : CohomologicalSpectralSequence ModR 0) (i : ℤ) (j : ℕ) : ModR :=
  (E.page 1).X (-i, -(j : ℤ))

/-- The map on `Tor_j^R(-,M)` induced by the chain differential `K_i ⟶ K_(i-1)`. -/
@[stacks 061Z "page-one differential map of the terms-first Tor spectral sequence"]
abbrev secondPageOneMap
    (K : ChainComplex ModR ℤ) (M : ModR) (i : ℤ) (j : ℕ) :
    secondPageOne K M i j ⟶ secondPageOne K M (i - 1) j :=
  ((Tor ModR j).map (K.d i (i - 1))).app M

/-- A spectral sequence converges to the homology of `K ⊗[R]^L M` when it comes from a
convergent filtered complex with the displayed homological reindexing of its abutment. -/
@[stacks 061Z "convergence predicate for the Tor spectral sequences"]
def ConvergesTo
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  ∃ F : FilteredComplex ModR,
    FilteredComplex.Cohomology.Convergence.Converges F E ∧
      ∀ n : ℤ, Nonempty (F.underlying.homology (-n) ≅ abutment K M n)

namespace ConvergesTo

/-- The filtered-complex specification of convergence to derived tensor homology. -/
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K : ChainComplex ModR ℤ} {M : ModR} :
    ConvergesTo E K M ↔
      ∃ F : FilteredComplex ModR,
        FilteredComplex.Cohomology.Convergence.Converges F E ∧
          ∀ n : ℤ, Nonempty (F.underlying.homology (-n) ≅ abutment K M n) := Iff.rfl

end ConvergesTo

/-- The first Tor spectral sequence has page two `Tor_j^R(H_i(K),M)` and the derived tensor
homology abutment. -/
@[stacks 061Z "homology-first Tor spectral-sequence predicate"]
def IsFirst
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  (∀ (i : ℤ) (j : ℕ), Nonempty (firstPageTwoObject E i j ≅ firstPageTwo K M i j)) ∧
    ConvergesTo E K M

namespace IsFirst

/-- The page-two and convergence clauses of the first Tor spectral sequence. -/
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K : ChainComplex ModR ℤ} {M : ModR} :
    IsFirst E K M ↔
      (∀ (i : ℤ) (j : ℕ), Nonempty (firstPageTwoObject E i j ≅ firstPageTwo K M i j)) ∧
        ConvergesTo E K M := Iff.rfl

/-- The first Tor spectral sequence has the displayed page-two entries. -/
theorem pageTwo
    {E : CohomologicalSpectralSequence ModR 0} {K : ChainComplex ModR ℤ} {M : ModR}
    (h : IsFirst E K M) (i : ℤ) (j : ℕ) :
    Nonempty (firstPageTwoObject E i j ≅ firstPageTwo K M i j) := h.1 i j

/-- The first Tor spectral sequence converges to derived tensor homology. -/
theorem converges
    {E : CohomologicalSpectralSequence ModR 0} {K : ChainComplex ModR ℤ} {M : ModR}
    (h : IsFirst E K M) : ConvergesTo E K M := h.2

end IsFirst

/-- The second Tor spectral sequence has page one `Tor_j^R(K_i,M)`, with differential induced
by the differential of `K`, and the derived tensor homology abutment. -/
@[stacks 061Z "terms-first Tor spectral-sequence predicate"]
def IsSecond
    (E : CohomologicalSpectralSequence ModR 0) (K : ChainComplex ModR ℤ) (M : ModR) : Prop :=
  (∃ pageOneIso : ∀ (i : ℤ) (j : ℕ),
      secondPageOneObject E i j ≅ secondPageOne K M i j,
    ∀ (i : ℤ) (j : ℕ),
      CommSq ((E.page 1).d (-i, -(j : ℤ)) (-(i - 1), -(j : ℤ))) (pageOneIso i j).hom
        (pageOneIso (i - 1) j).hom (secondPageOneMap K M i j)) ∧
    ConvergesTo E K M

namespace IsSecond

/-- The page-one differential and convergence clauses of the second Tor spectral sequence. -/
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K : ChainComplex ModR ℤ} {M : ModR} :
    IsSecond E K M ↔
      (∃ pageOneIso : ∀ (i : ℤ) (j : ℕ),
          secondPageOneObject E i j ≅ secondPageOne K M i j,
        ∀ (i : ℤ) (j : ℕ),
          CommSq ((E.page 1).d (-i, -(j : ℤ)) (-(i - 1), -(j : ℤ)))
            (pageOneIso i j).hom (pageOneIso (i - 1) j).hom (secondPageOneMap K M i j)) ∧
        ConvergesTo E K M := Iff.rfl

/-- The second Tor spectral sequence converges to derived tensor homology. -/
theorem converges
    {E : CohomologicalSpectralSequence ModR 0} {K : ChainComplex ModR ℤ} {M : ModR}
    (h : IsSecond E K M) : ConvergesTo E K M := h.2

end IsSecond

/-- Example 15.62.1 (1): a bounded-below chain complex and a module admit the Tor spectral
sequence with page two `Tor_j^R(H_i(K),M)`. -/
@[stacks 061Z "(1) homology-first Tor spectral sequence"]
theorem existsFirst (K : ChainComplex ModR ℤ) (hK : IsBoundedBelow K) (M : ModR) :
    ∃ E : CohomologicalSpectralSequence ModR 0, IsFirst E K M := sorry

/-- Example 15.62.1 (2): a bounded-below chain complex and a module admit the Tor spectral
sequence with page one `Tor_j^R(K_i,M)`. -/
@[stacks 061Z "(2) terms-first Tor spectral sequence"]
theorem existsSecond (K : ChainComplex ModR ℤ) (hK : IsBoundedBelow K) (M : ModR) :
    ∃ E : CohomologicalSpectralSequence ModR 0, IsSecond E K M := sorry

/-- The two Tor spectral sequences may be chosen together. -/
@[stacks 061Z "paired Tor spectral sequences"]
theorem existsPair (K : ChainComplex ModR ℤ) (hK : IsBoundedBelow K) (M : ModR) :
    ∃ E₂ E₁ : CohomologicalSpectralSequence ModR 0,
      IsFirst E₂ K M ∧ IsSecond E₁ K M := by
  obtain ⟨E₂, h₂⟩ := existsFirst K hK M
  obtain ⟨E₁, h₁⟩ := existsSecond K hK M
  exact ⟨E₂, E₁, h₂, h₁⟩

end CategoryTheory.DerivedCategory.TorSpectralSequence
