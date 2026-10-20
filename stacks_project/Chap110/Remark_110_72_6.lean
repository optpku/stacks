module

public import ReasLib.AlgebraicGeometry.GroupScheme.ClassifyingStack.Abelian
public import ReasLib.AlgebraicGeometry.HomStack.NonAlgebraic
import StacksCheckRecall

/-!
# Non-effective formal objects for a non-algebraic Hom-stack

In the setup of Proposition 110.72.5, the Hom-stack of morphisms from `X` into
the classifying stack of fppf torsors under a constant abelian scheme has a
non-effective formal object, and that classifying stack is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Scheme.Hom
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/- Remark 110.72.6 (1): in the setup of Proposition 110.72.5, the Hom-stack
`homStack X (classifyingTorsors (constantAbelianScheme A0))` has a non-effective
formal object. This is the obstruction contradicting Aoki's Theorem 1.1. -/
@[stacks 0AFD]
#check (AlgebraicGeometry.HomStack.exists_not_isEffective_formalObject :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)),
    ∃ ξ : FormalObject (homStack X (classifyingTorsors (constantAbelianScheme A0))),
      ¬ FormalObject.IsEffective ξ)

/- Remark 110.72.6 (2): the classifying stack
`classifyingTorsors (constantAbelianScheme A0)` is separated, in the sense that
its diagonal is proper. Combined with `not_isAlgebraic`, this contradicts the
Erratum's claim that a Hom-stack `homStack Y Z` is algebraic whenever `Z` is
separated. -/
@[stacks 0AFD]
#check (AlgebraicGeometry.HomStack.classifyingTorsors_separated :
    ∀ {k : Type u} [Field k]
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0],
    Groupoids.Hom.has (@AlgebraicSpace.Proper (specPowerSeries k))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        (classifyingTorsors (constantAbelianScheme A0))))

end AlgebraicGeometry.HomStack
