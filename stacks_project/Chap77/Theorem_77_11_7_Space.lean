/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_28_5
public import stacks_project.Chap68.Lemma_68_17_2
public import stacks_project.Chap77.Definition_77_3_1_Purity
public import stacks_project.Chap77.Theorem_77_11_7_Functor

/-!
# Algebraic-space structure on the flat-in-dimensions functor

Under finite presentation of the morphism and module, and relative purity, the
`(Sch/S)` functor `F_n` is an algebraic space, and the structure map `F_n ⟶ Y`
is a monomorphism of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

namespace flatInDimensionsOverSFunctor

/-- If `f` and `ℱ` are of finite presentation and `ℱ` is pure relative to `Y`, then
the `(Sch/S)` flat-in-dimensions functor is an algebraic space. -/
theorem isAlgebraicSpace [FinitePresentation f] [ℱ.IsFinitePresentation]
    (h_pure : ℱ.IsPureOver f) :
    IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n) :=
  sorry

/-- If the `(Sch/S)` flat-in-dimensions functor is an algebraic space, then the
structure morphism `F_n ⟶ Y` is a monomorphism. -/
instance instMono_toY [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    Mono (toY f ℱ n) :=
  sorry

/-- If `f` and `ℱ` are of finite presentation and `ℱ` is pure relative to `Y`, then
the structure morphism `F_n ⟶ Y` is of finite presentation. -/
theorem finitePresentation_toY [FinitePresentation f] [ℱ.IsFinitePresentation]
    (h_pure : ℱ.IsPureOver f)
    [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    FinitePresentation (toY f ℱ n) :=
  sorry

end flatInDimensionsOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Flattening
