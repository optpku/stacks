/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RationalEquivalence

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap67.Lemma_67_23_2
public import stacks_project.Chap67.Lemma_67_40_5
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed
public import stacks_project.Chap82.Definition_82_2_5_DeltaDimension
public import stacks_project.Chap82.Definition_82_15_1_ClosedPushforward
public import stacks_project.Chap82.Definition_82_17_1_Cycle

/-!
# Rational equivalence of cycles on algebraic spaces

In the good setup of Situation 82.2.1, a locally finite family of integral
closed subspaces of δ-dimension `k + 1` together with rational units determines
a `k`-cycle by pushing forward principal Weil divisors. Rational equivalence is
the resulting subgroup of `Z_k(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open Function Set Topology

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

namespace RationalEquivalence

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]

variable (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.RationalEquivalence.rationallyEquivalent_iff_sub_mem :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
    [IsDimensionFunction δ] (k : ℤ) (α β : cycleGroup f δ k),
    RationallyEquivalent f δ k α β ↔ α - β ∈ boundaries f δ k)

end RationalEquivalence

end AlgebraicGeometry.AlgebraicSpace
