module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor spectral sequences

This leaf records the two cohomological spectral sequences attached to a pair of bounded-above
derived modules.  Their pages use the canonical derived tensor product, while convergence is
stated through the reusable filtered-complex convergence predicate.

@stack 0662
-/

@[expose] public section

open CategoryTheory
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.TensorSpectralSequence

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "DModMinus" => DerivedCategory.Minus ModR
local notation "H" => DerivedCategory.homologyFunctor ModR
local notation "single₀" => DerivedCategory.singleFunctor ModR (0 : ℤ)

/-- The common abutment entry `H^n(K ⊗[R]^L L)` of the derived tensor spectral sequences. -/
@[stacks 0662 "derived tensor spectral-sequence abutment"]
abbrev abutment (K L : DModMinus) (n : ℤ) : ModR :=
  (H n).obj (K.obj ⊗[R]^L L.obj)

/-- The right-cohomology page-two entry `H^p(K ⊗[R]^L H^q(L))`. -/
@[stacks 0662 "right-cohomology page-two term"]
abbrev rightPageTwo (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj (K.obj ⊗[R]^L (single₀).obj ((H q).obj L.obj))

/-- The left-cohomology page-two entry `H^p(H^q(K) ⊗[R]^L L)`. -/
@[stacks 0662 "left-cohomology page-two term"]
abbrev leftPageTwo (K L : DModMinus) (p q : ℤ) : ModR :=
  (H p).obj ((single₀).obj ((H q).obj K.obj) ⊗[R]^L L.obj)

/-- A spectral sequence converges to derived tensor cohomology when it comes from a convergent
filtered complex whose underlying cohomology identifies with the derived tensor abutment. -/
@[stacks 0662 "derived tensor convergence"]
def ConvergesTo
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  ∃ F : FilteredComplex ModR,
    FilteredComplex.Cohomology.Convergence.Converges F E ∧
      ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ abutment K L n)

namespace ConvergesTo

/-- The source-semantic specification of convergence to derived tensor cohomology. -/
@[stacks 0662 "derived tensor convergence specification"]
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K L : DModMinus} :
    ConvergesTo E K L ↔
      ∃ F : FilteredComplex ModR,
        FilteredComplex.Cohomology.Convergence.Converges F E ∧
          ∀ n : ℤ, Nonempty (F.underlying.homology n ≅ abutment K L n) := sorry

end ConvergesTo

/-- A right-cohomology derived tensor spectral sequence has page two
`H^p(K ⊗[R]^L H^q(L))` and converges to `H^(p+q)(K ⊗[R]^L L)`. -/
@[stacks 0662 "right-cohomology tensor spectral sequence"]
def IsRightCohomology
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ, Nonempty ((E.page 2).X (p, q) ≅ rightPageTwo K L p q)) ∧
    ConvergesTo E K L

namespace IsRightCohomology

/-- The page-two and convergence clauses of a right-cohomology derived tensor spectral
sequence. -/
@[stacks 0662 "right-cohomology spectral-sequence specification"]
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K L : DModMinus} :
    IsRightCohomology E K L ↔
      (∀ p q : ℤ, Nonempty ((E.page 2).X (p, q) ≅ rightPageTwo K L p q)) ∧
        ConvergesTo E K L := sorry

/-- A right-cohomology derived tensor spectral sequence has the stated page-two entries. -/
@[stacks 0662 "right-cohomology page-two identification"]
theorem pageTwo
    {E : CohomologicalSpectralSequence ModR 0} {K L : DModMinus}
    (h : IsRightCohomology E K L) (p q : ℤ) :
    Nonempty ((E.page 2).X (p, q) ≅ rightPageTwo K L p q) := sorry

/-- A right-cohomology derived tensor spectral sequence converges to the common abutment. -/
@[stacks 0662 "right-cohomology convergence consequence"]
theorem converges
    {E : CohomologicalSpectralSequence ModR 0} {K L : DModMinus}
    (h : IsRightCohomology E K L) : ConvergesTo E K L := sorry

end IsRightCohomology

/-- A left-cohomology derived tensor spectral sequence has page two
`H^p(H^q(K) ⊗[R]^L L)` and converges to `H^(p+q)(K ⊗[R]^L L)`. -/
@[stacks 0662 "left-cohomology tensor spectral sequence"]
def IsLeftCohomology
    (E : CohomologicalSpectralSequence ModR 0) (K L : DModMinus) : Prop :=
  (∀ p q : ℤ, Nonempty ((E.page 2).X (p, q) ≅ leftPageTwo K L p q)) ∧
    ConvergesTo E K L

namespace IsLeftCohomology

/-- The page-two and convergence clauses of a left-cohomology derived tensor spectral
sequence. -/
@[stacks 0662 "left-cohomology spectral-sequence specification"]
theorem spec
    {E : CohomologicalSpectralSequence ModR 0} {K L : DModMinus} :
    IsLeftCohomology E K L ↔
      (∀ p q : ℤ, Nonempty ((E.page 2).X (p, q) ≅ leftPageTwo K L p q)) ∧
        ConvergesTo E K L := sorry

/-- A left-cohomology derived tensor spectral sequence has the stated page-two entries. -/
@[stacks 0662 "left-cohomology page-two identification"]
theorem pageTwo
    {E : CohomologicalSpectralSequence ModR 0} {K L : DModMinus}
    (h : IsLeftCohomology E K L) (p q : ℤ) :
    Nonempty ((E.page 2).X (p, q) ≅ leftPageTwo K L p q) := sorry

/-- A left-cohomology derived tensor spectral sequence converges to the common abutment. -/
@[stacks 0662 "left-cohomology convergence consequence"]
theorem converges
    {E : CohomologicalSpectralSequence ModR 0} {K L : DModMinus}
    (h : IsLeftCohomology E K L) : ConvergesTo E K L := sorry

end IsLeftCohomology

/-- Example 15.62.4 (1): bounded-above derived modules admit the right-cohomology derived tensor
spectral sequence. -/
@[stacks 0662 "(1) right-cohomology spectral sequence"]
theorem existsRightCohomology (K L : DModMinus) :
    ∃ E : CohomologicalSpectralSequence ModR 0, IsRightCohomology E K L := sorry

/-- Example 15.62.4 (2): bounded-above derived modules admit the left-cohomology derived tensor
spectral sequence. -/
@[stacks 0662 "(2) left-cohomology spectral sequence"]
theorem existsLeftCohomology (K L : DModMinus) :
    ∃ E : CohomologicalSpectralSequence ModR 0, IsLeftCohomology E K L := sorry

/-- The two derived tensor spectral sequences may be chosen together. -/
@[stacks 0662 "paired derived tensor spectral sequences"]
theorem existsPair (K L : DModMinus) :
    ∃ E_right E_left : CohomologicalSpectralSequence ModR 0,
      IsRightCohomology E_right K L ∧ IsLeftCohomology E_left K L := sorry

/-- Example 15.62.4 (3): the page-two differential of a cohomological spectral sequence has
target bidegree `(p + 2, q - 1)`. -/
@[stacks 0662 "(3) page-two differential"]
abbrev pageTwoDifferential
    (E : CohomologicalSpectralSequence ModR 0) (p q : ℤ) :
    (E.page 2).X (p, q) ⟶ (E.page 2).X (p + 2, q - 1) :=
  (E.page 2).d (p, q) (p + 2, q - 1)

end CategoryTheory.DerivedCategory.TensorSpectralSequence
