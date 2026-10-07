module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.CategoryTheory.Homology.DoubleComplex.ProductTotal

/-!
# Total Complexes of Coaugmented Coresolutions

@stack 0H0Q
@stack 0EYX
@stack 0E1Q
@stack 09J0

This file specializes the axis-comparison API to a cochain complex of cochain complexes reindexed
along `ComplexShape.embeddingUpNat`. Both coproduct and product totalizations use the same
zeroth-column map, so the coaugmentation relation is stated once and reused by both constructions.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂.CoaugmentedResolution

section ComparisonMaps

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The cohomological double complex obtained by extending the outer degree of a cochain complex
of cochain complexes from `ℕ` to `ℤ`. -/
@[stacks 0E1Q, stacks 09J0 "reindexed coaugmented coresolution"]
abbrev bicomplex (A : CochainComplex (CochainComplex C ℤ) ℕ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  A.extend embeddingUpNat

/-- Reindexing a cochain complex of cochain complexes from outer degree `ℕ` to the
cohomological double-complex grading `ℤ`. -/
@[stacks 0E1Q, stacks 09J0 "functorial reindexing of a coaugmented coresolution"]
abbrev bicomplexFunctor :
    CochainComplex (CochainComplex C ℤ) ℕ ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  embeddingUpNat.extendFunctor (CochainComplex C ℤ)

/-- The map of reindexed double complexes induced by a map of cochain complexes of cochain
complexes. -/
@[stacks 0E1Q, stacks 09J0 "map of reindexed coaugmented coresolutions"]
abbrev bicomplexMap {A B : CochainComplex (CochainComplex C ℤ) ℕ} (f : A ⟶ B) :
    bicomplex A ⟶ bicomplex B :=
  bicomplexFunctor.map f

/-- The canonical identification between the zeroth column of the reindexed coresolution and its
original degree-zero cochain complex. -/
@[stacks 0E1Q, stacks 09J0 "coaugmented zeroth-column identification"]
noncomputable abbrev zeroColumnIso
    (A : CochainComplex (CochainComplex C ℤ) ℕ) :
    (bicomplex A).X 0 ≅ A.X 0 :=
  A.extendXIso embeddingUpNat rfl

/-- The map into the zeroth column of the reindexed coresolution induced by a coaugmentation
`M ⟶ A.X 0`. -/
@[stacks 0E1Q, stacks 09J0 "coaugmentation zeroth-column map"]
noncomputable abbrev zeroColumnMap
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) :
    M ⟶ (bicomplex A).X 0 :=
  coaugmentation ≫ (zeroColumnIso A).inv

/-- The coaugmentation relation says exactly that the zeroth-column map is killed by the outgoing
horizontal differential of the reindexed coresolution. -/
@[stacks 0E1Q, stacks 09J0 "coaugmentation zeroth-column cycle condition"]
theorem zeroColumnMap_comp_d
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0) :
    zeroColumnMap A coaugmentation ≫ (bicomplex A).d 0 1 = 0 := sorry

/-- The short complex consisting of a coaugmentation and the first differential of its
coresolution. -/
@[stacks 0E1Q "the initial short complex of a coaugmented coresolution"]
abbrev shortComplex
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0) :
    ShortComplex (CochainComplex C ℤ) :=
  { X₁ := M
    X₂ := A.X 0
    X₃ := A.X 1
    f := coaugmentation
    g := A.d 0 1
    zero := h_coaugmentation }

namespace ToTotal

/-- The canonical map from a coaugmentation target into the coproduct total of its reindexed
coresolution. -/
@[stacks 0E1Q "the coaugmentation-to-total comparison"]
noncomputable def map [HasCountableCoproducts C]
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0) :
    M ⟶ HomologicalComplex₂.total (bicomplex A) (up ℤ) :=
  ZeroColumn.ToTotal.map (zeroColumnMap A coaugmentation)
    ((ZeroColumn.comp_d_eq_zero_iff (A := bicomplex A)
      (zeroColumnMap A coaugmentation)).mp
      (zeroColumnMap_comp_d A coaugmentation h_coaugmentation))

/-- The coproduct-total comparison is independent of the proof of the coaugmentation relation. -/
theorem map_proof_irrel [HasCountableCoproducts C]
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0)
    (h h' : coaugmentation ≫ A.d 0 1 = 0) :
    map A coaugmentation h = map A coaugmentation h' := sorry

end ToTotal

namespace ToProductTotal

/-- The canonical map from a coaugmentation target into the product total of its reindexed
coresolution. -/
@[stacks 09J0 "the coaugmentation-to-product-total comparison"]
noncomputable def map [HasCountableProducts C]
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0) :
    M ⟶ ProductTotal.complex (bicomplex A) :=
  ProductTotal.ZeroColumn.ToTotal.map (zeroColumnMap A coaugmentation)
    (zeroColumnMap_comp_d A coaugmentation h_coaugmentation)

/-- The product-total comparison is independent of the proof of the coaugmentation relation. -/
theorem map_proof_irrel [HasCountableProducts C]
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0)
    (h h' : coaugmentation ≫ A.d 0 1 = 0) :
    map A coaugmentation h = map A coaugmentation h' := sorry

end ToProductTotal

end ComparisonMaps

section Opcycles

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/-- The shifted rowwise cokernel complex associated to a cochain complex of cochain complexes. -/
@[stacks 09J0 "shifted rowwise cokernel complex"]
abbrev opcycles (A : CochainComplex (CochainComplex C ℤ) ℕ) (q : ℤ) :
    CochainComplex C ℕ :=
  ((opcyclesFunctor C (up ℤ) (q + 1)).mapHomologicalComplex (up ℕ)).obj A

/-- Applying shifted opcycles to a coaugmentation relation gives the zero composite needed for
the coaugmented row of cokernels. -/
theorem opcyclesMap_comp_d
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0)
    (q : ℤ) :
    opcyclesMap coaugmentation (q + 1) ≫ (opcycles A q).d 0 1 = 0 := sorry

/-- The coaugmented short complex on the shifted rowwise cokernels in vertical degree `q`. -/
@[stacks 09J0 "coaugmented short complex on shifted rowwise cokernels"]
noncomputable abbrev opcyclesShortComplex
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0)
    (q : ℤ) : ShortComplex C :=
  ShortComplex.mk (opcyclesMap coaugmentation (q + 1)) ((opcycles A q).d 0 1)
    (opcyclesMap_comp_d A coaugmentation h_coaugmentation q)

end Opcycles

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ToTotal

/-- In an abelian category with exact countable coproducts, an exact coaugmented coresolution
computes its source by the coproduct total complex. -/
@[stacks 0E1Q "an exact coaugmented coresolution computes its source by totalization"]
theorem quasiIso_of_exact
    [HasCountableCoproducts C] [CountableAB4 C]
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0)
    [Mono coaugmentation]
    (h_exact_zero : (shortComplex A coaugmentation h_coaugmentation).Exact)
    (h_exact : ∀ n : ℕ, A.ExactAt (n + 1)) :
    QuasiIso (map A coaugmentation h_coaugmentation) := sorry

end ToTotal

namespace ToProductTotal

/-- Exactness of a coaugmented coresolution and of all shifted rowwise cokernel complexes makes
the canonical map into its product total a quasi-isomorphism. -/
@[stacks 09J0 "exact coaugmented rows and exact cokernel rows compute a product total"]
theorem quasiIso_of_exact_opcycles
    [HasCountableProducts C]
    {M : CochainComplex C ℤ} (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (coaugmentation : M ⟶ A.X 0) (h_coaugmentation : coaugmentation ≫ A.d 0 1 = 0)
    [Mono coaugmentation]
    (h_exact_zero : (shortComplex A coaugmentation h_coaugmentation).Exact)
    (h_exact : ∀ n : ℕ, A.ExactAt (n + 1))
    (h_opcycles_mono : ∀ q : ℤ, Mono (opcyclesMap coaugmentation (q + 1)))
    (h_opcycles_exact_zero : ∀ q : ℤ,
      (opcyclesShortComplex A coaugmentation h_coaugmentation q).Exact)
    (h_opcycles_exact : ∀ q : ℤ, ∀ n : ℕ, (opcycles A q).ExactAt (n + 1)) :
    QuasiIso (map A coaugmentation h_coaugmentation) := sorry

end ToProductTotal

namespace ProductTotal

/-- Exact countable products turn diagonal acyclicity of a cochain sequence into
degree-zero acyclicity of its product total. -/
@[stacks 0H0Q "diagonal acyclicity for a product total"]
theorem isZero_homology_zero_of_diagonal
    [HasCountableProducts C] [CountableAB4Star C]
    (A : CochainComplex (CochainComplex C ℤ) ℕ)
    (hA : ∀ p : ℕ, IsZero ((A.X p).homology (-(p : ℤ)))) :
    IsZero ((HomologicalComplex₂.ProductTotal.complex (bicomplex A)).homology 0) := sorry

/-- In an abelian category with exact countable products, a columnwise quasi-isomorphism of
cochain sequences induces a quasi-isomorphism on product totals. -/
@[stacks 0EYX "columnwise quasi-isomorphisms induce product-total quasi-isomorphisms"]
theorem map_quasiIso_of_columnwise
    [HasCountableProducts C] [CountableAB4Star C]
    {A B : CochainComplex (CochainComplex C ℤ) ℕ} (f : A ⟶ B)
    (hf : ∀ p : ℕ, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.ProductTotal.functor.map (bicomplexMap f)) := sorry

end ProductTotal

end Abelian

end HomologicalComplex₂.CoaugmentedResolution
