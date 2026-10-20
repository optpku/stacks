/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
import StacksCheckRecall

/-!
# Lemma 12.26.3

Source-facing checks for the product total of a coaugmented cochain complex of cochain complexes.
The shared owner exposes the comparison map and the shifted rowwise-cokernel exactness criterion
without rebuilding opposite-category transport in this chapter file.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]
variable {M : CochainComplex C ℤ}
variable (A : CochainComplex (CochainComplex C ℤ) ℕ)
variable (ι : M ⟶ A.X 0) (hι hι' : ι ≫ A.d 0 1 = 0) (q : ℤ)

/- The shifted opcycles construction is the canonical rowwise-cokernel owner. -/
#check (HomologicalComplex₂.CoaugmentedResolution.opcycles A q :
  CochainComplex C ℕ)
#check (HomologicalComplex₂.CoaugmentedResolution.opcyclesShortComplex A ι hι q :
  ShortComplex C)

/- The product-total comparison is obtained from the generic zeroth-column comparison and is
independent of the proof supplied for the coaugmentation relation. -/
#check (HomologicalComplex₂.CoaugmentedResolution.ToProductTotal.map A ι hι :
  M ⟶ HomologicalComplex₂.ProductTotal.complex
    (HomologicalComplex₂.CoaugmentedResolution.bicomplex A))
#check (HomologicalComplex₂.CoaugmentedResolution.ToProductTotal.map_proof_irrel
  A ι hι hι' :
  HomologicalComplex₂.CoaugmentedResolution.ToProductTotal.map A ι hι =
    HomologicalComplex₂.CoaugmentedResolution.ToProductTotal.map A ι hι')

section

variable [CountableAB4Star C] [Mono ι]
variable
  (hExact₀ : (HomologicalComplex₂.CoaugmentedResolution.shortComplex A ι hι).Exact)
  (hExact : ∀ n : ℕ, A.ExactAt (n + 1))
  (hOpcyclesMono : ∀ q : ℤ, Mono (opcyclesMap ι (q + 1)))
  (hOpcyclesExact₀ : ∀ q : ℤ,
    (HomologicalComplex₂.CoaugmentedResolution.opcyclesShortComplex A ι hι q).Exact)
  (hOpcyclesExact : ∀ q : ℤ, ∀ n : ℕ,
    (HomologicalComplex₂.CoaugmentedResolution.opcycles A q).ExactAt (n + 1))

/- Lemma 12.26.3 [09J0]: in an abelian category with exact countable products, exactness of the
coaugmented row and every shifted rowwise-cokernel complex makes the canonical map into the product
total a quasi-isomorphism. -/
@[stacks 09J0]
#check (HomologicalComplex₂.CoaugmentedResolution.ToProductTotal.quasiIso_of_exact_opcycles
  A ι hι hExact₀ hExact hOpcyclesMono hOpcyclesExact₀ hOpcyclesExact :
    QuasiIso (HomologicalComplex₂.CoaugmentedResolution.ToProductTotal.map A ι hι))

end
