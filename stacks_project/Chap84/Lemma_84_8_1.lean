/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.EtaleComparison
import StacksCheckRecall

/-!
# Lemma 84.8.1

The canonical comparison units identify the ph inverse image of a small étale
sheaf with its small-to-big inverse image and recover the original sheaf.
Positive higher direct images vanish for locally torsion abelian sheaves.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn

universe u

/- Lemma 84.8.1 (1a): the ε comparison unit identifies ε_*a⁻¹F with π⁻¹F. -/
@[stacks 0DGT] #check
  (AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilon_pushforward_aInverseImage_unit_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
      IsIso ((epsilon X).adjunction.unit.app (((siteMorphismOfTopoi X)⁻¹).obj F)))

/- Lemma 84.8.1 (1b): the composite comparison unit identifies a_*a⁻¹F with F. -/
@[stacks 0DGT] #check (AlgebraicGeometry.AlgebraicSpace.PhComparison.toSmallEtale_unit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))),
    IsIso ((toSmallEtale X).adjunction.unit.app F))

/- Lemma 84.8.1 (2): positive higher ε-direct images vanish for locally torsion sheaves. -/
@[stacks 0DGT] #check (AlgebraicGeometry.AlgebraicSpace.PhComparison.epsilon_rightDerived_aInverseImage_isZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}), F.IsLocallyTorsion → ∀ (i : ℕ), 0 < i →
    IsZero (((comparisonTopologyPushforwardAb etale_le_ph X).rightDerived i).obj
      ((aInverseImage X).obj F)))

end
