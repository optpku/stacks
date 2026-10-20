/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Definition_66_25_2_RegularAt
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap89.Lemma_89_4_2_PointBlowupSequence

/-!
# Making a finitely supported ideal invertible by point blowups
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 89.4.3: Let `S` be a scheme. Let `X` be a Noetherian algebraic space over
`S`. Let `T ⊂ |X|` be a finite set of closed points `x` such that `X` is regular at
`x` and the local ring of `X` at `x` has dimension `2`. Let `I ⊂ 𝒪_X` be a
quasi-coherent sheaf of ideals such that `𝒪_X / I` is supported on `T`. Then there
exists a sequence `X_m ⟶ ⋯ ⟶ X_0 = X` of blowups at closed points lying over `T`
such that the inverse-image ideal `I.pullback s.toSource` is an invertible ideal
sheaf. -/
@[stacks 0BHG]
theorem existsInvertibleIdealAfterPointBlowups {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsNoetherian X] (T : Set (Points X))
    (hT_finite : T.Finite) (hT_closed : T ⊆ closedPoints (Points X))
    (hT_regular : ∀ x, x ∈ T → RegularAt X x)
    (hT_dimension : ∀ x, x ∈ T → localRingDimAt x = 2)
    (I : IdealSubobject X) [IsQuasiCoherent I]
    (hI_support : (ClosedSubspace.ofQuasiCoherentIdeal I).pointsSet ⊆ T) :
    ∃ (Xn : AlgebraicSpace S) (s : PointBlowupSequence X Xn),
      s.EveryCenterOver T ∧ isInvertibleObject (I.pullback s.toSource).toModule :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
