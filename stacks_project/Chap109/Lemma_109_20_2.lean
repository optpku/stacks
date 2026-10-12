/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import stacks_project.Chap109.Definition_109_20_1_Prestable
public import stacks_project.Chap109.Lemma_109_18_1_Substack

/-!
# Prestable curves

There is an open substack 𝒞urves^{prestable} ⊂ 𝒞urves classifying prestable
families of curves, equivalently proper schemes over a field whose
singularities are at-worst-nodal, of dimension 1, and with H⁰(X, 𝒪_X) = k.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.20.2 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{prestable}` if and only if
`X ⟶ S` is a prestable family of curves. -/
@[stacks 0E6U]
theorem classifying_factorsThrough_prestable_iff
    {S : Scheme.{u}} (P : Obj S) :
    prestable S P ↔ Prestable (hom P) :=
  sorry

/-- Lemma 109.20.2 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{prestable}` if and only if the singularities of `X` are
at-worst-nodal, `dim(X) = 1`, and `k = H⁰(X, 𝒪_X)`. -/
@[stacks 0E6U]
theorem classifying_factorsThrough_prestable_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    prestable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
