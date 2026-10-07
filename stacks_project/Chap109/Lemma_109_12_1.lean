module

public import stacks_project.Chap109.Lemma_109_12_1_Substack

/-!
# Gorenstein curves

There is an open substack 𝒞urves^{Gorenstein} ⊂ 𝒞urves classifying Gorenstein
families of curves, equivalently proper Gorenstein schemes of dimension at most
one over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.12.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{Gorenstein}` if and only if
`X ⟶ S` is Gorenstein. -/
@[stacks 0E1M]
theorem classifying_factorsThrough_gorenstein_iff
    {S : Scheme.{u}} (P : Obj S) :
    gorenstein S P ↔ AlgebraicSpace.Gorenstein (hom P) :=
  sorry

/-- Lemma 109.12.1 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{Gorenstein}` if and only if `X` is Gorenstein. -/
@[stacks 0E1M]
theorem classifying_factorsThrough_gorenstein_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    gorenstein (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.Gorenstein X.left :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
