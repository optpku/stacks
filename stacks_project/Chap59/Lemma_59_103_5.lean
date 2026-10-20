/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_103_5_Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.HComparison
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

/- Lemma 59.103.5 (1a). -/
@[stacks 0EWF] #check (AlgebraicGeometry.Scheme.HComparison.epsilon_pushforward_aInverseImage_unit_isIso :
  ∀ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion),
    IsIso
      ((comparisonTopologyAdjunction AddCommGrpCat.{u + 1} etale_le_h X).unit.app
        ((AlgebraicGeometry.Scheme.FppfEtale.piInverseImage X).obj F)))

/- Lemma 59.103.5 (1b). -/
@[stacks 0EWF] #check (AlgebraicGeometry.Scheme.HComparison.epsilon_rightDerived_aInverseImage_isZero :
  ∀ {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i),
    IsZero
      (((comparisonTopologyPushforwardAb etale_le_h X).rightDerived i).obj
        ((aInverseImage X).obj F)))

/- Lemma 59.103.5 (2). -/
@[stacks 0EWF] #check (AlgebraicGeometry.Scheme.HComparison.proper_aInverseImage_higherDirectImage :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ),
    IsIsomorphic
      ((aInverseImage Y).obj (((AlgebraicGeometry.Scheme.PhComparison.smallPushforwardAb f).rightDerived i).obj F))
      ((Derived.Over.pushforwardDegree hPrecoverage.toGrothendieck f i).obj
        ((aInverseImage X).obj F)))

/- Lemma 59.103.5 (3). -/
@[stacks 0EWF] #check (AlgebraicGeometry.Scheme.HComparison.plus_piInverseImage_unit_isIso :
  ∀ {X : Scheme.{u}}
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K),
    IsIso
      ((Derived.Plus.unit etale_le_h X).app ((plusPiInverseImage X).obj K)))

/- Lemma 59.103.5 (4). -/
@[stacks 0EWF] #check (AlgebraicGeometry.Scheme.HComparison.proper_plusSmallHPushforward_isIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion X.smallEtaleTopology) K),
    IsIso ((plusSmallHPushforwardHom f).app K))

end

end
