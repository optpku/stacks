/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic
public import stacks_project.Chap109.Lemma_109_15_2_Substack

/-!
# Local complete intersection curves with isolated singularities

The open substack `𝒞urves^{lci+} = 𝒞urves^{lci} ∩ 𝒞urves^{+} ⊂ 𝒞urves`
has smooth structure morphism to `Spec(Z)`. A family of curves is classified
by it if and only if it is a local complete intersection and its nonsmooth
locus, with any/some closed subspace structure, is finite over the base.
A proper scheme of dimension at most one over a field is classified by it if
and only if it is a local complete intersection over that field and smooth
except at finitely many points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.15.2 (1): the structure morphism `𝒞urves^{lci+} ⟶ Spec(Z)` is
smooth. -/
@[stacks 0DZX]
instance instSmooth_lciPlus (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (lciPlus S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- Lemma 109.15.2 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{lci+}` if and only if
`X ⟶ S` is a local complete intersection morphism and the singular locus of
`X ⟶ S` endowed with any/some closed subspace structure is finite over `S`. -/
@[stacks 0DZX]
theorem classifying_factorsThrough_lciPlus_iff {S : Scheme.{u}} (P : Obj S) :
    lciPlus S P ↔
      AlgebraicSpace.IsLocalCompleteIntersection (hom P) ∧
        ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed (hom P)),
          IsFinite (T.ι ≫ hom P) :=
  sorry

/-- Lemma 109.15.2 (3): given `X` a proper scheme over a field `k` of
dimension `≤ 1`, the classifying morphism `Spec k ⟶ 𝒞urves` factors through
`𝒞urves^{lci+}` if and only if `X` is a local complete intersection over `k`
and `X ⟶ Spec k` is smooth except at finitely many points. -/
@[stacks 0DZX]
theorem classifying_factorsThrough_lciPlus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    lciPlus (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      IsLocalCompleteIntersectionOver k X.hom ∧
        Set.Finite (setOf fun x : X.left ↦ ¬ X.hom.SmoothAt x) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
