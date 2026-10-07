module

public import stacks_project.Chap84.Lemma_84_6_1_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.6.1

For a sheaf of sets `F` on the small étale site of an algebraic space `X`,
`ε_{X,*}(a_X⁻¹ F) = π_X⁻¹ F` and `a_{X,*}(a_X⁻¹ F) = F`. For an abelian sheaf,
the higher direct images `R^i ε_{X,*}(a_X⁻¹ F)` vanish for `i > 0`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FppfEtale

/-- Lemma 84.6.1 (1): for a sheaf of sets `F` on `X_étale`, the canonical map
`π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
@[stacks 0DGF]
theorem epsilon_pushforward_aInverse_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((Fppf.epsilon X).adjunction.unit.app ((siteMorphismOfTopoi X)⁻¹.obj F)) :=
  sorry

/-- Lemma 84.6.1 (2): for a sheaf of sets `F` on `X_étale`, the canonical map
`F ⟶ a_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
@[stacks 0DGF]
theorem fppfComparison_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((fppfComparison X).adjunction.unit.app F) := sorry

/-- Lemma 84.6.1 (3): for an abelian sheaf `F` on `X_étale` and `0 < i`, the higher
direct images `R^i ε_{X,*}(a_X⁻¹ F)` vanish. -/
@[stacks 0DGF]
theorem aInverse_higherDirectImage_isZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ) (hi : 0 < i) :
    IsZero (((epsilonPushforward X).rightDerived i).obj ((aInverseAb X).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FppfEtale

end

end
