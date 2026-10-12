/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap79.Proposition_79_12_11
public import stacks_project.Chap79.Remark_79_12_12_Fold

/-!
# Separatedness cannot be dropped from the finite-part algebraicity criterion

The fold of the affine line with doubled origin onto `A¹_k` is locally of finite
type but not separated. Its finite-part functor has four points over `0`, of
which only three lift along étale morphisms to `Y`, so `(X/Y)_fin` is not an
algebraic space étale over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

variable (k : Type u) [Field k]

/-- Remark 79.12.12 (1): the fold of the affine line with doubled origin onto
`A¹_k` is locally of finite type. -/
@[stacks 04QI, instance]
instance instLocallyOfFiniteType_foldMorphism :
    LocallyOfFiniteType (foldMorphism k) :=
  sorry

/-- Remark 79.12.12 (2): the fold of the affine line with doubled origin onto
`A¹_k` is not separated. -/
@[stacks 04QI]
theorem not_separated_foldMorphism : ¬ Separated (foldMorphism k) :=
  sorry

/-- Remark 79.12.12 (3): over `0 ∈ Y` there are two distinct points `0₁` and
`0₂` in the fibre `Spec k ×_Y X`. -/
@[stacks 04QI]
theorem originPoint_ne : originPoint k 0 ≠ originPoint k 1 :=
  sorry

/-- Remark 79.12.12 (4): `(X/Y)_fin` has four points over `0`, namely the
finite-part pairs classified by subsets of `{0₁, 0₂}`. -/
@[stacks 04QI]
theorem eq_pointOfSubset_iff (p : Point (foldMorphism k) (originOver k)) :
    p.a = originToY k ↔ ∃ s : Set (Fin 2), p = pointOfSubset k s :=
  sorry

/-- Remark 79.12.12 (5): of the four points over `0`, the empty set and the two
singletons lift to an open of `U ×_Y X` finite over an étale morphism `U ⟶ Y`. -/
@[stacks 04QI]
theorem isEtaleLiftable_pointOfSubset_of_ne_univ {s : Set (Fin 2)}
    (hs : s ≠ Set.univ) :
    IsEtaleLiftable (pointOfSubset k s) :=
  sorry

/-- Remark 79.12.12 (6): the finite-part point `{0₁, 0₂}` over `0` does not lift
to an open of `U ×_Y X` finite over an étale morphism `U ⟶ Y`. -/
@[stacks 04QI]
theorem not_isEtaleLiftable_univ :
    ¬ IsEtaleLiftable (pointOfSubset k (Set.univ : Set (Fin 2))) :=
  sorry

/-- The structure morphism `(X/Y)_fin ⟶ Y` obtained if the finite-part functor
of the fold is an algebraic space. -/
def foldFinitePartHom [IsAlgebraicSpace (finitePart (foldMorphism k))] :
    ofIsAlgebraicSpace (finitePart (foldMorphism k)) ⟶ ofOver (affineLineOver k) :=
  toY (foldMorphism k)

/-- `foldFinitePartHom` is the functor-of-points morphism `toY`. -/
theorem foldFinitePartHom_eq [IsAlgebraicSpace (finitePart (foldMorphism k))] :
    foldFinitePartHom k = toY (foldMorphism k) :=
  sorry

/-- Remark 79.12.12 (7): if `(X/Y)_fin` were representable by an algebraic space,
the structure morphism `(X/Y)_fin ⟶ Y` would not be étale. -/
@[stacks 04QI]
theorem not_etale_foldFinitePart_of_isAlgebraicSpace
    [IsAlgebraicSpace (finitePart (foldMorphism k))] :
    ¬ Etale (foldFinitePartHom k) :=
  sorry

/-- Remark 79.12.12 (8): `(X/Y)_fin` is not an algebraic space, so separatedness
cannot be dropped from Proposition 79.12.11. -/
@[stacks 04QI]
theorem not_isAlgebraicSpace_foldFinitePart :
    ¬ IsAlgebraicSpace (finitePart (foldMorphism k)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
