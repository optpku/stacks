/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Quotient
public import stacks_project.Chap96.Proposition_96_14_3_Comparison
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap75.Lemma_75_21_1_Pullback
public import stacks_project.Chap78.Lemma_78_12_3_QCoh
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap96.Lemma_96_11_3_Pullback
public import stacks_project.Chap96.Lemma_96_13_2
import StacksCheckRecall

/-! # Quasi-coherent modules on a quotient stack -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver AlgebraicGeometry.GroupoidAlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- Reconstruction of an equivariant module on the quotient stack. -/
abbrev fromGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : G.QCoh ⥤ QCoh (SmallQuotient.quotientStack G) :=
  QuotientQCoh.fromGroupoidStack G

end AlgebraicGeometry.GroupoidsOver.QCoh

/- Proposition 96.14.3. For any groupoid in algebraic spaces over a scheme,
quasi-coherent modules on its quotient stack are equivalent to equivariant
quasi-coherent modules on the groupoid. -/
@[stacks 06WT] #check (AlgebraicGeometry.GroupoidsOver.QCoh.toGroupoidEquivalence :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
    AlgebraicGeometry.GroupoidsOver.QCoh
      (AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient.quotientStack G) ≌ G.QCoh)
