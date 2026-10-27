/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions.OverS
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Implications

/-!
# Algebraic-space structure on the flat-in-dimensions functor

Under finite presentation of the morphism and module, and relative purity, the
flat-in-dimensions functor is an algebraic space whose structural morphism is a
monomorphism of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

namespace flatInDimensionsOverSFunctor

/-- If `f` and `ℱ` are of finite presentation and `ℱ` is pure relative to `Y`,
then the flat-in-dimensions functor on schemes over `S` is an algebraic space. -/
theorem isAlgebraicSpace [FinitePresentation f] [ℱ.IsFinitePresentation]
    (h_pure : ℱ.IsPureOver f) :
    IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n) :=
  sorry

/-- If the flat-in-dimensions functor is an algebraic space, then its structural
morphism to `Y` is a monomorphism. -/
instance instMono_toY [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    Mono (toY f ℱ n) :=
  sorry

/-- If `f` and `ℱ` are of finite presentation and `ℱ` is pure relative to `Y`,
then the structural morphism of the flat-in-dimensions space is of finite presentation. -/
theorem finitePresentation_toY [FinitePresentation f] [ℱ.IsFinitePresentation]
    (h_pure : ℱ.IsPureOver f)
    [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    FinitePresentation (toY f ℱ n) :=
  sorry

end flatInDimensionsOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Flattening
