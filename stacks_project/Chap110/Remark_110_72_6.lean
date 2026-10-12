/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap98.Definition_98_9_4_Effective
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap110.Proposition_110_72_5

/-!
# Non-effective formal objects for a non-algebraic Hom-stack

In the setup of Proposition 110.72.5, the Hom-stack of morphisms from `X` into
the classifying stack of fppf torsors under a constant abelian scheme has a
non-effective formal object, and that classifying stack is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.GroupScheme
open AlgebraicGeometry.GroupoidScheme
open AlgebraicGeometry.GroupoidAlgebraicSpace
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Scheme.Hom
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.HomStack

/-- The spectrum of the formal power series ring `k⟦t⟧` is locally Noetherian. -/
instance instIsLocallyNoetherian_specPowerSeries {k : Type u} [Field k] :
    IsLocallyNoetherian (specPowerSeries k) :=
  sorry

/-- The classifying stack of fppf torsors under the constant abelian scheme
associated to an abelian variety is algebraic. -/
instance instAlgebraicStack_classifyingTorsors {k : Type u} [Field k]
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] :
    AlgebraicStack (classifyingTorsors (constantAbelianScheme A0)) :=
  sorry

/-- Remark 110.72.6 (1): in the setup of Proposition 110.72.5, the Hom-stack
`homStack X (classifyingTorsors (constantAbelianScheme A0))` has a non-effective
formal object. This is the obstruction contradicting Aoki's Theorem 1.1. -/
@[stacks 0AFD]
theorem exists_not_isEffective_formalObject {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ¬ IsAlgebraicClosureOfFiniteField k)
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] (hA0 : ¬ IsIso A0.hom)
    (X : Over (specPowerSeries k)) [Projective X.hom] [Flat X.hom]
    (h_connected : ∀ s : specPowerSeries k,
      GeometricallyConnected (X.hom.fiberToSpecResidueField s))
    (h_dim : ∀ s : specPowerSeries k, topologicalKrullDim (X.hom.fiber s) = 1)
    (h_regular : Scheme.Regular X.left)
    (h_loop : IsNodalWithRationalComponentLoop (specialFiber X)) :
    ∃ ξ : FormalObject (homStack X (classifyingTorsors (constantAbelianScheme A0))),
      ¬ FormalObject.IsEffective ξ :=
  sorry

/-- Remark 110.72.6 (2): the classifying stack
`classifyingTorsors (constantAbelianScheme A0)` is separated, in the sense that
its diagonal is proper. Combined with `not_isAlgebraic`, this contradicts the
Erratum's claim that a Hom-stack `homStack Y Z` is algebraic whenever `Z` is
separated. -/
@[stacks 0AFD]
theorem classifyingTorsors_separated {k : Type u} [Field k]
    (A0 : SchemeOverField k) [GrpObj A0] [AbelianVariety A0] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper (specPowerSeries k))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        (classifyingTorsors (constantAbelianScheme A0))) :=
  sorry

end AlgebraicGeometry.HomStack
