/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import stacks_project.Chap109.Lemma_109_9_1_Substack

/-!
# Curves with universally trivial pushforward of 𝒪 and fibres of dimension 1

There is an open substack 𝒞urves^{h0, 1} ⊂ 𝒞urves classifying families of
curves for which 𝒪_S ⟶ f_* 𝒪_X is an isomorphism after every base change
and every fibre has dimension 1, equivalently proper schemes of dimension 1
over a field with H^0(X, 𝒪_X) = k.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.9.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{h0, 1}` if and only if
`𝒪_S ⟶ f_* 𝒪_X` is an isomorphism after every base change (including the
identity) and the fibres of `X ⟶ S` have dimension `1`. -/
@[stacks 0E6I]
theorem classifying_factorsThrough_h0Dim1_iff
    {S : Scheme.{u}} (P : Obj S) :
    h0Dim1 S P ↔
      (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
        ∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1 :=
  sorry

/-- Lemma 109.9.1 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{h0, 1}` if and only if `H^0(X, 𝒪_X) = k` and `dim(X) = 1`. -/
@[stacks 0E6I]
theorem classifying_factorsThrough_h0Dim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    h0Dim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        topologicalKrullDim X.left = 1 :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
