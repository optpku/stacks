module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.CategoryTheory.Homology.DoubleComplex.ProductTotal
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison.Descent

/-!
# Total Complexes of Augmented Resolutions

This file specializes the axis-comparison API to a chain complex of cochain complexes reindexed
along `ComplexShape.embeddingDownNat`.  The augmentation relation is explicit input to every map;
there is no fallback map when that relation is absent.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂.AugmentedResolution

section ComparisonMaps

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The cohomological double complex obtained by extending the outer degree of a chain complex
of cochain complexes from `ℕ` to `ℤ`. -/
@[stacks 09IZ, stacks 0E1R "reindexed augmented resolution"]
abbrev bicomplex (A : ChainComplex (CochainComplex C ℤ) ℕ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  A.extend embeddingDownNat

/-- The canonical identification between the zeroth column of the reindexed resolution and its
original degree-zero cochain complex. -/
@[stacks 09IZ, stacks 0E1R "augmented zeroth-column identification"]
noncomputable abbrev zeroColumnIso
    (A : ChainComplex (CochainComplex C ℤ) ℕ) :
    (bicomplex A).X 0 ≅ A.X 0 :=
  A.extendXIso embeddingDownNat (neg_zero : -(0 : ℤ) = 0)

/-- The map from the zeroth column of the reindexed resolution induced by an augmentation
`A.X 0 ⟶ M`. -/
@[stacks 09IZ, stacks 0E1R "augmentation zeroth-column map"]
noncomputable abbrev zeroColumnMap
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) :
    (bicomplex A).X 0 ⟶ M :=
  (zeroColumnIso A).hom ≫ augmentation

/-- The augmentation relation says exactly that the zeroth-column map kills the horizontal
differential entering the zeroth column of the reindexed resolution. -/
@[stacks 09IZ, stacks 0E1R "augmentation zeroth-column cycle condition"]
theorem incoming_comp_zero
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0) :
    (bicomplex A).d (-1) 0 ≫
      zeroColumnMap A augmentation = 0 := sorry

/-- The short complex consisting of the first differential of a resolution and its
augmentation. -/
@[stacks 09IZ "the initial short complex of an augmented resolution"]
abbrev shortComplex
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0) :
    ShortComplex (CochainComplex C ℤ) :=
  { X₁ := A.X 1
    X₂ := A.X 0
    X₃ := M
    f := A.d 1 0
    g := augmentation
    zero := h_augmentation }

namespace FromTotal

/-- The canonical map from the coproduct total of a reindexed resolution to its augmentation
target. -/
@[stacks 09IZ "the total-to-augmentation comparison"]
noncomputable def map [HasCountableCoproducts C]
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0) :
    HomologicalComplex₂.total (bicomplex A) (up ℤ) ⟶ M :=
  ZeroColumn.FromTotal.map (zeroColumnMap A augmentation)
    (incoming_comp_zero A augmentation h_augmentation)

/-- The augmented-resolution total map is independent of the proof of the augmentation
relation. -/
theorem map_proof_irrel [HasCountableCoproducts C]
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M)
    (h h' : A.d 1 0 ≫ augmentation = 0) :
    map A augmentation h = map A augmentation h' := sorry

end FromTotal

namespace FromProductTotal

/-- The canonical map from the product total of a reindexed resolution to its augmentation
target. -/
@[stacks 0E1R "the product-total-to-augmentation comparison"]
noncomputable def map [HasCountableProducts C]
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0) :
    ProductTotal.complex (bicomplex A) ⟶ M :=
  ProductTotal.ZeroColumn.FromTotal.map (zeroColumnMap A augmentation)
    (incoming_comp_zero A augmentation h_augmentation)

/-- The augmented-resolution product-total map is independent of the proof of the augmentation
relation. -/
theorem map_proof_irrel [HasCountableProducts C]
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M)
    (h h' : A.d 1 0 ≫ augmentation = 0) :
    map A augmentation h = map A augmentation h' := sorry

end FromProductTotal

end ComparisonMaps

section Cycles

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/-- The chain complex obtained by applying degree-`p` cycles to every cochain complex in an
outer chain complex. -/
abbrev cycles (A : ChainComplex (CochainComplex C ℤ) ℕ) (p : ℤ) : ChainComplex C ℕ :=
  ((cyclesFunctor C (up ℤ) p).mapHomologicalComplex (down ℕ)).obj A

/-- Applying cycles to an augmentation relation gives the zero composite needed for the
augmented cycles row. -/
theorem cyclesMap_comp_zero
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0)
    (p : ℤ) :
    (cycles A p).d 1 0 ≫ cyclesMap augmentation p = 0 := sorry

/-- The augmented short complex obtained by applying degree-`p` cycles to the resolution. -/
@[stacks 09IZ "the cycles short complex of an augmented resolution"]
noncomputable abbrev cyclesShortComplex
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0)
    (p : ℤ) : ShortComplex C :=
  ShortComplex.mk ((cycles A p).d 1 0) (cyclesMap augmentation p)
    (cyclesMap_comp_zero A augmentation h_augmentation p)

end Cycles

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FromTotal

/-- Exactness of an augmented resolution and of all its cycles rows makes the canonical map from
the coproduct total to the augmentation target a quasi-isomorphism. -/
@[stacks 09IZ "exact augmented rows and exact cycles rows compute the augmentation target"]
theorem quasiIso_of_exact_cycles [HasCountableCoproducts C]
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0)
    (h_exact_zero : (shortComplex A augmentation h_augmentation).Exact)
    (h_exact : ∀ n : ℕ, A.ExactAt (n + 1))
    (h_cycles_exact_zero : ∀ p : ℤ,
      (cyclesShortComplex A augmentation h_augmentation p).Exact)
    (h_cycles_exact : ∀ p : ℤ, ∀ n : ℕ, (cycles A p).ExactAt (n + 1)) :
    QuasiIso (map A augmentation h_augmentation) := sorry

end FromTotal

namespace FromProductTotal

/-- In an abelian category with exact countable products, an exact augmented resolution computes
its target by the product total complex. -/
@[stacks 0E1R "an exact augmented resolution computes its target by product totalization"]
theorem quasiIso_of_exact
    [HasCountableProducts C] [CountableAB4Star C]
    {M : CochainComplex C ℤ} (A : ChainComplex (CochainComplex C ℤ) ℕ)
    (augmentation : A.X 0 ⟶ M) (h_augmentation : A.d 1 0 ≫ augmentation = 0)
    (h_exact_zero : (shortComplex A augmentation h_augmentation).Exact)
    [Epi augmentation] (h_exact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    QuasiIso (map A augmentation h_augmentation) := sorry

end FromProductTotal

end Abelian

end HomologicalComplex₂.AugmentedResolution
