/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions.Representation
import StacksCheckRecall

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

variable [FinitePresentation f] [ℱ.IsFinitePresentation] (h_pure : ℱ.IsPureOver f)

/- Theorem 77.11.7: Under finite presentation and relative purity, the
flat-in-dimensions functor is an algebraic space. -/
@[stacks 0CX1] #check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsOverSFunctor.isAlgebraicSpace
    f ℱ n h_pure : IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n))

variable [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)]

#check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsOverSFunctor.instMono_toY f ℱ n :
    Mono (toY f ℱ n))

#check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsOverSFunctor.finitePresentation_toY
    f ℱ n h_pure : FinitePresentation (toY f ℱ n))

end flatInDimensionsOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Flattening
