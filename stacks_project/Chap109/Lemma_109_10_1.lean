/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import stacks_project.Chap109.Lemma_109_10_1_Substack

/-!
# Geometrically reduced curves

There is an open substack 𝒞urves^{geomred} ⊂ 𝒞urves classifying families of
curves with geometrically reduced fibres, equivalently proper geometrically
reduced schemes of dimension at most one over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.10.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{geomred}` if and only if the
fibres of `X ⟶ S` are geometrically reduced. -/
@[stacks 0E0G]
theorem classifying_factorsThrough_geometricallyReduced_iff
    {S : Scheme.{u}} (P : Obj S) :
    geometricallyReduced S P ↔
      ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P) :=
  sorry

/-- Lemma 109.10.1 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{geomred}` if and only if `X` is geometrically reduced over
`k`. -/
@[stacks 0E0G]
theorem classifying_factorsThrough_geometricallyReduced_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    geometricallyReduced (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.geometricallyReduced X :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
