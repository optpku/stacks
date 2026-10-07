module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Lemma_84_6_5_Comparison
public import stacks_project.Chap84.Lemma_84_6_6_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.6.5

In the setup of Lemma 84.6.4, a proper morphism of algebraic spaces identifies
`a_Y⁻¹ ∘ f_small,*` with `f_big,fppf,* ∘ a_X⁻¹` on sheaves of sets, and identifies
`a_Y⁻¹(R f_small,* K)` with `R f_big,fppf,* (a_X⁻¹ K)` on `D⁺(X_étale)` when the
cohomology sheaves of `K` are locally torsion. Here `a_X = π_X ∘ ε_X` and
`a_Y = π_Y ∘ ε_Y`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

/-- Lemma 84.6.5 (1): in the setup of Lemma 84.6.4, if `f : X ⟶ Y` is a proper morphism
of algebraic spaces over a scheme `S`, then the functors `a_Y⁻¹ ∘ f_small,*` and
`f_big,fppf,* ∘ a_X⁻¹` from sheaves of sets on `X_étale` to sheaves of sets on
`(Spaces/Y)_fppf` are canonically isomorphic via `smallFppfPushforwardHom`. -/
@[stacks 0DGJ]
theorem proper_smallFppfPushforward_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f] :
    IsIso (smallFppfPushforwardHom f) := sorry

/-- Lemma 84.6.5 (2): in the setup of Lemma 84.6.4, if `f : X ⟶ Y` is proper and `K` is
in `D⁺(X_étale)` with locally torsion cohomology sheaves, then the canonical mate
`a_Y⁻¹(R f_small,* K) ⟶ R f_big,fppf,* (a_X⁻¹ K)` is an isomorphism. -/
@[stacks 0DGJ]
theorem proper_derivedPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) K) :
    IsIso (derivedBaseChangeApp f K) := sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
