/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_103_5_Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.HComparison
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Lemma 59.103.5 (1): for a scheme `X` and a locally torsion abelian sheaf `F` on
`X_étale`, the topology-comparison adjunction unit identifies
`ε_{X,*} (a_X⁻¹ F)` with `π_X⁻¹ F`. -/
@[stacks 0EWF]
theorem epsilon_pushforward_aInverseImage_unit_isIso {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) :
    IsIso
      ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_h X).unit.app
        ((piInverseImage X).obj F)) := sorry

/-- Lemma 59.103.5 (2): for a scheme `X`, a locally torsion abelian sheaf `F` on
`X_étale`, and `0 < i`, the higher direct images `R^i ε_{X,*} (a_X⁻¹ F)` vanish. -/
@[stacks 0EWF]
theorem epsilon_rightDerived_aInverseImage_isZero {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb etale_le_h X).rightDerived i).obj
        ((aInverseImage X).obj F)) := sorry

/-- Lemma 59.103.5 (3): for a proper morphism `f : X ⟶ Y` of schemes and a locally
torsion abelian sheaf `F` on `X_étale`, inverse image along `a` identifies
`R^i f_small,* F` with `R^i f_big,h,* (a_X⁻¹ F)`. -/
@[stacks 0EWF]
theorem proper_aInverseImage_higherDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) :
    IsIsomorphic
      ((aInverseImage Y).obj (((smallPushforwardAb f).rightDerived i).obj F))
      ((Derived.Over.pushforwardDegree hPrecoverage.toGrothendieck f i).obj
        ((aInverseImage X).obj F)) := sorry

/-- Lemma 59.103.5 (4): for a scheme `X` and `K` in `D⁺(X_étale)` with torsion
cohomology sheaves, the comparison unit `π_X⁻¹ K ⟶ Rε_{X,*} (a_X⁻¹ K)` is an
isomorphism. -/
@[stacks 0EWF]
theorem plus_piInverseImage_unit_isIso {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso
      ((Derived.Plus.unit etale_le_h X).app ((plusPiInverseImage X).obj K)) :=
  sorry

/-- Lemma 59.103.5 (5): for a proper morphism `f : X ⟶ Y` of schemes and `K` in
`D⁺(X_étale)` with torsion cohomology sheaves, the canonical mate
`a_Y⁻¹ (Rf_small,* K) ⟶ Rf_big,h,* (a_X⁻¹ K)` is an isomorphism. -/
@[stacks 0EWF]
theorem proper_plusSmallHPushforward_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K) :
    IsIso ((plusSmallHPushforwardHom f).app K) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
