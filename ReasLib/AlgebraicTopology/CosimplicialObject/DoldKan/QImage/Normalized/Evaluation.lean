/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.QImage.Normalized
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Evaluation of the canonical normalized image quotient

Evaluation of a cokernel of cochain complexes in an abelian category is the cokernel of the
evaluated morphism. This leaf exposes that comparison for the canonical normalized quotient,
together with both quotient-map coordinates.

@stack 019I
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized

variable {A : Type u} [Category.{v} A] [Preadditive A]
variable [HasImages (ChainComplex Aᵒᵖ ℕ)] [HasCokernels (CochainComplex A ℕ)]
variable (U : CosimplicialObject A) (n : ℕ)
variable [HasCokernel ((degenerate.ι U).f n)]
variable [PreservesColimit (parallelPair (degenerate.ι U) 0)
  (HomologicalComplex.eval A (ComplexShape.up ℕ) n)]

/-- Evaluation of the canonical normalized quotient is the cokernel of the evaluated degenerate
inclusion. -/
@[stacks 019I "degreewise canonical normalized cokernel comparison"]
noncomputable def evalCokernelIso :
    (obj U).X n ≅ cokernel ((degenerate.ι U).f n) :=
  PreservesCokernel.iso (HomologicalComplex.eval A (ComplexShape.up ℕ) n)
    (degenerate.ι U)

namespace evalCokernelIso

/-- The evaluated normalized quotient map followed by the comparison is the component cokernel
projection. -/
@[reassoc, stacks 019I "forward degreewise normalized quotient coordinate"]
theorem π_f_comp_hom :
    (π U).f n ≫ (evalCokernelIso U n).hom = cokernel.π ((degenerate.ι U).f n) := sorry

/-- The component cokernel projection followed by the inverse comparison is the evaluated
normalized quotient map. -/
@[reassoc, stacks 019I "inverse degreewise normalized quotient coordinate"]
theorem π_comp_inv :
    cokernel.π ((degenerate.ι U).f n) ≫ (evalCokernelIso U n).inv = (π U).f n := sorry

end evalCokernelIso

end CategoryTheory.CosimplicialObject.DoldKan.degenerate.normalized
