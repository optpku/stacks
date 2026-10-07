module

public import stacks_project.Chap109.Lemma_109_8_1_Substack

/-!
# Cohen–Macaulay curves

There is an open substack 𝒞urves^{CM} ⊂ 𝒞urves classifying Cohen–Macaulay
families of curves, equivalently proper Cohen–Macaulay schemes of dimension
at most one over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.8.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{CM}` if and only if `X ⟶ S`
is Cohen–Macaulay. -/
@[stacks 0E0I]
theorem classifying_factorsThrough_cohenMacaulay_iff
    {S : Scheme.{u}} (P : Obj S) :
    cohenMacaulay S P ↔ AlgebraicSpace.CohenMacaulay (hom P) :=
  sorry

/-- Lemma 109.8.1 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{CM}` if and only if `X` is Cohen–Macaulay. -/
@[stacks 0E0I]
theorem classifying_factorsThrough_cohenMacaulay_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    cohenMacaulay (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Scheme.CohenMacaulay X.left :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
