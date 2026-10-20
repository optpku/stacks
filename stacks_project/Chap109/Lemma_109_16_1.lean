/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.Topology.KrullDimension.Equidimensional
public import stacks_project.Chap109.Lemma_109_16_1_Substack

/-!
# Smooth curves

There are open substacks `𝒞urves^{smooth, 1} ⊂ 𝒞urves^{smooth} ⊂ 𝒞urves`
classifying smooth families of curves, equivalently proper smooth schemes of
dimension at most one over a field, and the relative-dimension-1 open
substack thereof.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.16.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{smooth}` if and only if
`X ⟶ S` is smooth. -/
@[stacks 0DZZ]
theorem classifying_factorsThrough_smooth_iff
    {S : Scheme.{u}} (P : Obj S) :
    smooth S P ↔ AlgebraicSpace.Smooth (hom P) :=
  sorry

/-- Lemma 109.16.1 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{smooth, 1}` if and only if
`X ⟶ S` is smooth of relative dimension 1. -/
@[stacks 0DZZ]
theorem classifying_factorsThrough_smoothDim1_iff
    {S : Scheme.{u}} (P : Obj S) :
    smoothDim1 S P ↔
      AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- Lemma 109.16.1 (3): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{smooth}` if and only if `X` is smooth over `k`. -/
@[stacks 0DZZ]
theorem classifying_factorsThrough_smooth_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    smooth (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom :=
  sorry

/-- Lemma 109.16.1 (4): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{smooth, 1}` if and only if `X` is smooth over `k` and
equidimensional of dimension 1. Nonemptiness of `X` blocks the empty proper
scheme over `k`. -/
@[stacks 0DZZ]
theorem classifying_factorsThrough_smoothDim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1) :
    smoothDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom ∧
        TopologicalSpace.EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
