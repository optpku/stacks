/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Comparison
import StacksCheckRecall

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
open scoped MorphismOfTopoiIn

universe u

/- Lemma 84.6.1 (1a): the canonical map
`π_X⁻¹ F ⟶ ε_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
@[stacks 0DGF]
#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.epsilon_pushforward_aInverse_unit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    IsIso ((Fppf.epsilon X).adjunction.unit.app ((siteMorphismOfTopoi X)⁻¹.obj F)))

/- Lemma 84.6.1 (1b): the canonical map
`F ⟶ a_{X,*}(a_X⁻¹ F)` is an isomorphism. -/
@[stacks 0DGF]
#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.fppfComparison_unit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    IsIso ((fppfComparison X).adjunction.unit.app F))

/- Lemma 84.6.1 (2): for an abelian sheaf `F` and `0 < i`,
`R^i ε_{X,*}(a_X⁻¹ F)` vanishes. -/
@[stacks 0DGF]
#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.aInverse_higherDirectImage_isZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (i : ℕ) (hi : 0 < i),
    IsZero (((epsilonPushforward X).rightDerived i).obj ((aInverseAb X).obj F)))

end
