/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.AugmentedResolution
import StacksCheckRecall

/-!
# Lemma 12.26.2

Source-facing checks for an augmented chain complex of cochain complexes and its coproduct total.
The reusable comparison map, its explicit augmentation-compatibility input, and the exact-cycles
criterion are owned by `HomologicalComplex₂.AugmentedResolution` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
variable {M : CochainComplex C ℤ}
variable (A : ChainComplex (CochainComplex C ℤ) ℕ)
variable (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0)
variable (p : ℤ)

/- The reindexed double complex underlying every augmented-resolution totalization is a named
shared construction, rather than a repeated `extend embeddingDownNat` expression. -/
#check (HomologicalComplex₂.AugmentedResolution.bicomplex A :
  HomologicalComplex₂ C (up ℤ) (up ℤ))

/- The generic map out of a coproduct total is constructed from a map on the zeroth column
`A.X 0` (the source's horizontal degree-zero row) together with the condition that it kills the
incoming horizontal differential. -/
#check (HomologicalComplex₂.ZeroColumn.FromTotal.map
  (HomologicalComplex₂.AugmentedResolution.zeroColumnMap A augmentation)
  (HomologicalComplex₂.AugmentedResolution.incoming_comp_zero A augmentation h_augmentation) :
  HomologicalComplex₂.total (HomologicalComplex₂.AugmentedResolution.bicomplex A) (up ℤ) ⟶ M)

/- The augmented-resolution specialization requires the relation `A.d 1 0 ≫ augmentation = 0`
as an explicit argument; no unrelated zero map is returned when the relation is unavailable. -/
#check (HomologicalComplex₂.AugmentedResolution.FromTotal.map A augmentation h_augmentation :
  HomologicalComplex₂.total (HomologicalComplex₂.AugmentedResolution.bicomplex A) (up ℤ) ⟶ M)

/- The rowwise cycles complex and its augmentation relation are exposed independently for
downstream exactness arguments. -/
#check (HomologicalComplex₂.AugmentedResolution.cycles A p : ChainComplex C ℕ)
#check (HomologicalComplex₂.AugmentedResolution.cyclesMap_comp_zero
  A augmentation h_augmentation p :
  (HomologicalComplex₂.AugmentedResolution.cycles A p).d 1 0 ≫
    cyclesMap augmentation p = 0)
#check (HomologicalComplex₂.AugmentedResolution.shortComplex A augmentation h_augmentation :
  ShortComplex (CochainComplex C ℤ))
#check (HomologicalComplex₂.AugmentedResolution.cyclesShortComplex
  A augmentation h_augmentation p : ShortComplex C)

section Exactness

variable
  (hExact₀ : (HomologicalComplex₂.AugmentedResolution.shortComplex
    A augmentation h_augmentation).Exact)
  (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
  (hCyclesExact₀ : ∀ p : ℤ,
    (HomologicalComplex₂.AugmentedResolution.cyclesShortComplex
      A augmentation h_augmentation p).Exact)
  (hCyclesExact : ∀ p : ℤ, ∀ n : ℕ,
    (HomologicalComplex₂.AugmentedResolution.cycles A p).ExactAt (n + 1))

/- Lemma 12.26.2 [09IZ]: exactness of the augmented row and every row of cycles makes the
canonical map from the coproduct total to the augmentation target a quasi-isomorphism. -/
@[stacks 09IZ]
#check (HomologicalComplex₂.AugmentedResolution.FromTotal.quasiIso_of_exact_cycles
  A augmentation h_augmentation hExact₀ hExact hCyclesExact₀ hCyclesExact :
  QuasiIso (HomologicalComplex₂.AugmentedResolution.FromTotal.map A augmentation h_augmentation))

end Exactness
