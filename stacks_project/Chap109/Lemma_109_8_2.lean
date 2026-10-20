/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap109.Lemma_109_8_2_Substack

/-!
# Cohen–Macaulay curves of relative dimension 1

There is an open substack `𝒞urves^{CM, 1} ⊂ 𝒞urves` classifying Cohen–Macaulay
families of curves of relative dimension 1, equivalently proper Cohen–Macaulay
schemes that are equidimensional of dimension 1 over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.8.2 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{CM, 1}` if and only if
`X ⟶ S` is Cohen–Macaulay of relative dimension 1. -/
@[stacks 0E1F]
theorem classifying_factorsThrough_cohenMacaulayDim1_iff
    {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulayDim1 S P ↔
      AlgebraicSpace.CohenMacaulay (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- Lemma 109.8.2 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{CM, 1}` if and only if `X` is Cohen–Macaulay and
equidimensional of dimension 1. Nonemptiness of `X` is a formal side
condition. -/
@[stacks 0E1F]
theorem classifying_factorsThrough_cohenMacaulayDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    cohenMacaulayDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.CohenMacaulay X.left ∧ EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
