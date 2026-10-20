/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Composition.Basic

/-!
# Ground-Ring Tensor Models for Composed Derived Tensor Functors

This leaf owns the pointwise comparison between ordinary and derived tensor products of the
underlying cochain complexes of differential graded algebras. It uses that comparison to state
the source-faithful existence theorem for a bimodule representing a composite derived tensor
functor. The same-universe parameters here reflect Mathlib's current monoidal structure on
`ModuleCat`; the derived localization and the other composition leaves remain universe-aware.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DifferentialGradedCategory

namespace DifferentialGradedBimodule.Tensor.Derived

variable {R : Type u} [CommRing R]

namespace GroundTensor

/-- The underlying cochain complex of a DG algebra, regarded in the homotopy category of
`R`-modules. -/
@[stacks 0BZ8 "ground-ring underlying homotopy object"]
abbrev algebra (D : CochainDGAlgebra.{u, u} R) :
    HomotopyCategory (ModuleCat.{u} R) (up ℤ) :=
  (HomotopyCategory.quotient (ModuleCat.{u} R) (up ℤ)).obj D.toCochainComplex

/-- The canonical comparison from the two-variable derived tensor of `A` and `C` to their
ordinary tensor in the derived category of `R`-modules. -/
@[stacks 0BZ8 "ordinary tensor versus derived tensor"]
noncomputable def comparison (A C : CochainDGAlgebra.{u, u} R) :
    DerivedCategory.DerivedTensor.Bifunctor.obj
        ((DerivedCategory.Qh : HomotopyCategory (ModuleCat.{u} R) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{u} R)).obj (algebra A))
        ((DerivedCategory.Qh : HomotopyCategory (ModuleCat.{u} R) (up ℤ) ⥤
          DerivedCategory (ModuleCat.{u} R)).obj (algebra C)) ⟶
      (DerivedCategory.Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤
        DerivedCategory (ModuleCat.{u} R)).obj
          (A.toCochainComplex ⊗ C.toCochainComplex) :=
  DerivedCategory.DerivedTensor.Bifunctor.counitAppOfComplex
    A.toCochainComplex C.toCochainComplex

/-- The ground-ring comparison is the canonical derived-tensor counit evaluated on the two
underlying cochain complexes.  Downstream proofs should use this bridge instead of unfolding
the long derived-category object type in `comparison`. -/
@[simp, stacks 0BZ8 "ground-ring comparison factorization"]
theorem comparison_fac (A C : CochainDGAlgebra.{u, u} R) :
    comparison A C =
      DerivedCategory.DerivedTensor.Bifunctor.counitAppOfComplex
        A.toCochainComplex C.toCochainComplex := sorry

/-- The source-faithful condition that the ordinary tensor `A ⊗[R] C` represents the
derived tensor `A ⊗[R]ᴸ C`. -/
@[stacks 0BZ8 "ordinary tensor represents the derived tensor"]
def RepresentsDerived (A C : CochainDGAlgebra.{u, u} R) : Prop :=
  IsIso (comparison A C)

end GroundTensor

/-- Lemma 22.38.2 (0BZ8): if `A ⊗[R] C` represents `A ⊗[R]ᴸ C`, then the composite
of derived tensoring by `N` and `N'` is represented by some differential graded
`(A, C)`-bimodule. -/
@[stacks 0BZ8]
theorem existsComposite
    {A B C : CochainDGAlgebra.{u, u} R}
    (N : DifferentialGradedBimodule.{u, u, u, u} A B)
    (N' : DifferentialGradedBimodule.{u, u, u, u} B C)
    (hAC : GroundTensor.RepresentsDerived A C) :
    ∃ N'' : DifferentialGradedBimodule.{u, u, u, u} A C,
      RepresentsComposite N N' N'' := sorry

end DifferentialGradedBimodule.Tensor.Derived
