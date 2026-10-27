/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions.Limit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

section

/- Lemma 77.11.5 (1): In Situation 77.11.4, the functor `F_n` satisfies the
sheaf property for the fpqc topology. -/
@[stacks 0CWW] #check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor_isSheaf_fpqc f ℱ n :
    Presheaf.IsSheaf (SchemeOver.fpqcTopology Y)
      (Flattening.flatInDimensionsFunctor f ℱ n))

end

section

variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/- Lemma 77.11.5 (2): if `f` is quasi-compact and locally of finite presentation
and `ℱ` is of finite presentation, the functor `F_n` is limit preserving. -/
@[stacks 0CWW] #check
  (AlgebraicGeometry.AlgebraicSpace.Flattening.flatInDimensionsFunctor_preservesDirectedAffineLimits f ℱ n :
    SchemeOver.PreservesDirectedAffineLimits Y
      (Flattening.flatInDimensionsFunctor f ℱ n))

end
