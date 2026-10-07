module

public import stacks_project.Chap84.Lemma_84_6_2_Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.6.2

For `K` in `D⁺(X_étale)` on an algebraic space `X` over a scheme `S`, the
canonical maps `π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)` and `K ⟶ Ra_{X,*}(a_X⁻¹ K)` are
isomorphisms, where `a_X = π_X ∘ ε_X` is the morphism of topoi
`Sh((Spaces/X)_fppf) ⟶ Sh(X_étale)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

/-- Lemma 84.6.2 (1): for `K` in `D⁺(X_étale)`, the canonical map
`π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)` is an isomorphism. -/
@[stacks 0DGG]
theorem piInverseDerivedUnit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso (piInverseDerivedUnit X K) := sorry

/-- Lemma 84.6.2 (2): for `K` in `D⁺(X_étale)`, the derived adjunction unit
`K ⟶ Ra_{X,*}(a_X⁻¹ K)` is an isomorphism, where
`a_X : Sh((Spaces/X)_fppf) ⟶ Sh(X_étale)` is the composite `π_X ∘ ε_X`. -/
@[stacks 0DGG]
theorem plusAAdjunction_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIso ((plusAAdjunction X).unit.app K) := sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
