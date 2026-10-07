module

public import stacks_project.Chap59.Lemma_59_102_6_Adjunction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PhComparison
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- Lemma 59.102.6: for a scheme `X` and `K` in `D⁺(X_étale)` with torsion cohomology sheaves,
the derived adjunction unit `K ⟶ Ra_{X,*} (a_X⁻¹ K)` is an isomorphism, where
`a_X : Sh((Sch/X)_ph) ⟶ Sh(X_étale)` is the composite `π_X ∘ ε_X`. -/
@[stacks 0DE5]
theorem plusAAdjunction_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso ((plusAAdjunction (Over.mk (𝟙 X))).unit.app K) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
