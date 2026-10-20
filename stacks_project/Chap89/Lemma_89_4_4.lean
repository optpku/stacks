module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Definition_66_25_2_RegularAt
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IsomorphismLocus
public import stacks_project.Chap89.Lemma_89_4_2_PointBlowupSequence

/-!
# Domination of proper modifications by sequences of point blowups
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 89.4.4: Let `S` be a scheme. Let `X` be a Noetherian algebraic space over
`S`. Let `T ⊂ |X|` be a finite set of closed points `x` such that `X` is regular at
`x` and the local ring of `X` at `x` has dimension `2`. Let `f : Y ⟶ X` be a proper
morphism of algebraic spaces which is an isomorphism over `U = X \ T`. Then there
exists a sequence `X_n ⟶ ⋯ ⟶ X_0 = X` of blowups at closed points lying over `T`
and a factorization `X_n ⟶ Y ⟶ X` of the composition. -/
@[stacks 0BHH]
theorem exists_pointBlowupSequence_lift {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian X] (T : Set (Points X)) (hT_finite : T.Finite)
    (hT_closed : T ⊆ closedPoints (Points X))
    (hT_regular : ∀ x, x ∈ T → RegularAt X x)
    (hT_dimension : ∀ x, x ∈ T → localRingDimAt x = 2)
    (U : OpenSubspace X) (hU : U.pointsSet = Tᶜ) (f : Y ⟶ X) [Proper f]
    (h_iso : IsIso (restrictTo f U)) :
    ∃ (Xn : AlgebraicSpace S) (s : PointBlowupSequence X Xn) (g : Xn ⟶ Y),
      s.EveryCenterOver T ∧ g ≫ f = s.toSource :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
