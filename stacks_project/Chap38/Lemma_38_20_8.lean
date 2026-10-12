/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints.Limit
public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Flattening

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (p : ℕ)
variable [Smooth f] [GeometricallyIrreducible f]

section

variable [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- Lemma 38.20.8 (1): the generic-fibre rank-`p` freeness functor is a sheaf for the
fpqc topology. -/
@[stacks 05MS] #check
  (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor_isSheaf_fpqc f ℱ p :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor f ℱ p))

end

section

variable [ℱ.IsFinitePresentation]

/- Lemma 38.20.8 (2): if `ℱ` is of finite presentation, the generic-fibre rank-`p`
freeness functor preserves directed limits of affine schemes over `S`. -/
@[stacks 05MS] #check
  (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor_preservesDirectedAffineLimits
    f ℱ p :
    Scheme.Over.PreservesDirectedAffineLimits S
      (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor f ℱ p))

end

end AlgebraicGeometry.Scheme.Flattening
