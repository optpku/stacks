module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Limit
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open Scheme.Over

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)

section

variable [ℱ.IsQuasicoherent]

/- Lemma 38.20.14 (1): the flattening functor is a sheaf for the fpqc topology. -/
@[stacks 05MY] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.functor_isSheaf_fpqc f ℱ :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ))

end

section

variable [QuasiCompact f] [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]

/- Lemma 38.20.14 (2): if `f` is quasi-compact and locally of finite presentation and `ℱ`
is of finite presentation, the flattening functor preserves directed limits of affine schemes
over `S`. -/
@[stacks 05MY] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.functor_preservesDirectedAffineLimits f ℱ :
    PreservesDirectedAffineLimits S
      (AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ))

end

end AlgebraicGeometry
