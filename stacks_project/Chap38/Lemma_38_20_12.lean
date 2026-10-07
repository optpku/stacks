module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions.Limit
public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (n : ℕ)

section

variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- Lemma 38.20.12 (1): the flat-in-dimensions functor is a sheaf for the fpqc topology. -/
@[stacks 05MV] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor_isSheaf_fpqc f ℱ n :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor f ℱ n))

end

section

variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/- Lemma 38.20.12 (2): if `f` is quasi-compact and locally of finite presentation and `ℱ`
is of finite presentation, the flat-in-dimensions functor preserves directed limits of affine
schemes over `S`. -/
@[stacks 05MV] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor_preservesDirectedAffineLimits
    f ℱ n :
    Scheme.Over.PreservesDirectedAffineLimits S
      (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor f ℱ n))

end

end AlgebraicGeometry.Scheme.Flattening
