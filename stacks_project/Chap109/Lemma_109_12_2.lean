/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.KrullDimension.Equidimensional
public import stacks_project.Chap109.Lemma_109_12_2_Substack

/-!
# Gorenstein curves of relative dimension 1

There is an open substack `𝒞urves^{Gorenstein, 1} ⊂ 𝒞urves` classifying
Gorenstein families of curves of relative dimension 1, equivalently proper
Gorenstein schemes that are equidimensional of dimension 1 over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.12.2 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{Gorenstein, 1}` if and only if
`X ⟶ S` is Gorenstein of relative dimension 1. -/
@[stacks 0E6M]
theorem classifying_factorsThrough_gorensteinDim1_iff
    {S : Scheme.{u}} (P : Obj S) :
    gorensteinDim1 S P ↔
      AlgebraicSpace.Gorenstein (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- Lemma 109.12.2 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{Gorenstein, 1}` if and only if `X` is Gorenstein and
equidimensional of dimension 1. Nonemptiness of `X` is a formal side
condition. -/
@[stacks 0E6M]
theorem classifying_factorsThrough_gorensteinDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    gorensteinDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.Gorenstein X.left ∧ EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
