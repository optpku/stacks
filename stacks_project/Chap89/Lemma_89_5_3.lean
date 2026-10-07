module

public import stacks_project.Chap89.«89_3_0_1»
public import stacks_project.Chap89.Lemma_89_5_3_Sequence

/-!
# Equivalence of normalized-blowup factorizations under family excision
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- The reference to Strategy 89.3.0.1 includes the assumption that each U i is
affine. IsElementary alone only asserts that the residue-field point is mono. -/

/-- Lemma 89.5.3: Let `X`, `x i`, `U i ⟶ X`, `u i` be as in 89.3.0.1, including
affineness of each `U i`, and assume `f : Y ⟶ X` corresponds to `g i : Y i ⟶ U i`
under `F = excisionFamilyFunctor`. Assume `X` satisfies the equivalent conditions
of Morphisms of Spaces, Lemma 67.49.1. Then `f` factors as a finite sequence
of normalized blowups at closed points lying over `{x i}` if and only if each
`g i` factors as a finite sequence of normalized blowups at closed points
lying over `u i`. Here `g i` is the underlying structure morphism of the
`i`th coordinate of `F.obj Y`, `u i` is
`ofOver.pointsEquiv (U i).toOver (U i).point`, lying over is
`EveryCenterOver`, and Lemma 67.49.1 is
`HasFiniteIrreducibleComponentsOnCompactOpens X`. -/
@[stacks 0BHL]
theorem existsNormalizedBlowupSequence_iff {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) (hx_inj : Function.Injective x)
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary)
    (hU : supportedOnRange X x U) (Y : IsoOverClosedPoints X x hx) :
    (∃ s : NormalizedBlowupSequence X Y.obj.left,
        s.toSource = Y.obj.hom ∧ s.EveryCenterOver (Set.range x)) ↔
      ∀ i, ∃ s : NormalizedBlowupSequence (ofOver (U i).toOver)
          ((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj.left,
        s.toSource =
            ((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj.hom ∧
          s.EveryCenterOver {ofOver.pointsEquiv (U i).toOver (U i).point} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
