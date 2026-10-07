module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap75.Definition_75_9_1_Square

/-!
# Lemma 81.14.8

A proper dense open in a Noetherian algebraic space can be enlarged by an affine
étale chart to an elementary distinguished square whose pullback to the original
open still has dense image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.14.8. Let `S` be a scheme. Let `X` be a Noetherian algebraic space over
`S`. Let `U ⊂ X` be a proper dense open subspace. Then there exist an affine scheme
`V` over `S` and an étale morphism `f : ofOver V ⟶ X` such that the open subspace
`W` with `W.pointsSet = U.pointsSet ∪ Set.range (Points.map f)` is strictly larger
than `U`, `(U ⊂ W, V ⟶ W)` is an elementary distinguished square, and
`U ×_W V ⟶ U` has dense image. -/
@[stacks 0F4C]
theorem exists_affineEtale_enlarging_elementaryDistinguishedSquare
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (U : OpenSubspace X) (h_dense : Dense U.pointsSet)
    (h_ne : U.pointsSet ≠ Set.univ) :
    ∃ (V : Over S) (f : ofOver V ⟶ X) (W : OpenSubspace X)
      (j : U.X ⟶ W.X) (fW : ofOver V ⟶ W.X),
      AlgebraicGeometry.IsAffine V.left ∧ Etale f ∧
        W.pointsSet = U.pointsSet ∪ Set.range (Points.map f) ∧
          j ≫ W.ι = U.ι ∧ fW ≫ W.ι = f ∧ U.pointsSet ⊂ W.pointsSet ∧
            IsElementaryDistinguishedSquare j fW ∧
              Dense (Set.range (Points.map (pullback.fst j fW))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
