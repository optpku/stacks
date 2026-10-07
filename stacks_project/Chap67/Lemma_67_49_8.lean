module

public import stacks_project.Chap67.Lemma_67_49_5
public import stacks_project.Chap67.Definition_67_5_2_Surjective
import StacksCheckRecall

/-!
# Properties of the absolute normalization of an algebraic space

Lemma 67.49.8 records that the chosen absolute normalization `X.normalization`
of an algebraic space satisfying the equivalent conditions of Lemma 67.49.1 is
normal, that `X.normalizationTo` is integral and surjective, that it bijects
codimension-`0` points, and that morphisms from normal algebraic spaces sending
codimension-`0` points to codimension-`0` points lift uniquely through it.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.49.8 (1): let `S` be a scheme and let `X` be an algebraic space over
`S` satisfying the equivalent conditions of Lemma 67.49.1. Then the absolute
normalization `X.normalization` is a normal algebraic space. -/
@[stacks 0BB4] #check
  (instIsNormal_normalization :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [HasFiniteIrreducibleComponentsOnCompactOpens X],
      IsNormal X.normalization)

/- Lemma 67.49.8 (2): let `S` be a scheme and let `X` be an algebraic space over
`S` satisfying the equivalent conditions of Lemma 67.49.1. Then the canonical
morphism `X.normalizationTo` is integral. -/
@[stacks 0BB4] #check
  (instIsIntegralHom_normalizationTo :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [HasFiniteIrreducibleComponentsOnCompactOpens X],
      IsIntegralHom X.normalizationTo)

/-- Lemma 67.49.8 (3): let `S` be a scheme and let `X` be an algebraic space over
`S` satisfying the equivalent conditions of Lemma 67.49.1. Then the canonical
morphism `X.normalizationTo` is surjective. -/
@[stacks 0BB4]
instance instSurjective_normalizationTo {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Surjective X.normalizationTo :=
  sorry

namespace Normalization

/-- Lemma 67.49.8 (4): let `S` be a scheme and let `X` be an algebraic space over
`S` satisfying the equivalent conditions of Lemma 67.49.1. Then
`Points.map X.normalizationTo` induces a bijection between the sets of
codimension-`0` points of `X.normalization` and of `X`, in the sense of
Definition 66.10.2. -/
@[stacks 0BB4]
theorem bijOn_codimZeroPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Set.BijOn (Points.map X.normalizationTo)
      (codimZeroPoints X.normalization) (codimZeroPoints X) :=
  sorry

/-- Lemma 67.49.8 (5): let `S` be a scheme and let `X` be an algebraic space over
`S` satisfying the equivalent conditions of Lemma 67.49.1. If `Z` is a normal
algebraic space over `S` and `f : Z ⟶ X` sends every codimension-`0` point of
`Z` to a codimension-`0` point of `X`, then there is a unique factorization
`f = h ≫ X.normalizationTo`. -/
@[stacks 0BB4]
theorem existsUnique_lift_of_isNormal {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X] {Z : AlgebraicSpace S}
    [IsNormal Z] (f : Z ⟶ X) (hf : mapsCodimZero f) :
    ∃! h : Z ⟶ X.normalization, h ≫ X.normalizationTo = f :=
  sorry

end Normalization

end AlgebraicGeometry.AlgebraicSpace
