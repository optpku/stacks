/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_18_1_Substack

/-!
# Nodal curves

There is an open substack 𝒞urves^{nodal} ⊂ 𝒞urves classifying at-worst-nodal
families of curves of relative dimension 1, equivalently proper schemes over a
field whose singularities are at-worst-nodal and which are equidimensional of
dimension 1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.18.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{nodal}` if and only if
`X ⟶ S` is at-worst-nodal of relative dimension 1. -/
@[stacks 0DSY]
theorem classifying_factorsThrough_nodal_iff
    {S : Scheme.{u}} (P : Obj S) :
    nodal S P ↔ AlgebraicSpace.AtWorstNodal (hom P) :=
  sorry

/-- Lemma 109.18.1 (2): given a nonempty scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{nodal}` if and only if the singularities of `X` are
at-worst-nodal and `X` is equidimensional of dimension 1. -/
@[stacks 0DSY]
theorem classifying_factorsThrough_nodal_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    nodal (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        TopologicalSpace.EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
