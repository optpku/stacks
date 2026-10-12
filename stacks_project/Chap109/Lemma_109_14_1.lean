/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_14_1_SingularLocus
public import stacks_project.Chap109.Lemma_109_14_1_Substack

/-!
# Curves with isolated singularities

The open substack Curves⁺ ⊂ Curves classifies families of curves whose
nonsmooth locus is finite over the base, equivalently proper schemes of
dimension at most one over a field that are smooth except at finitely many
points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.14.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ Curves` factors through `Curves⁺` if and only if the singular
locus of `X ⟶ S` endowed with any/some closed subspace structure is finite
over `S`. -/
@[stacks 0DZW]
theorem classifying_factorsThrough_isolatedSingularities_iff
    {S : Scheme.{u}} (P : Obj S) :
    isolatedSingularities S P ↔
      ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed (hom P)),
        IsFinite (T.ι ≫ hom P) :=
  sorry

/-- Lemma 109.14.1 (2): given `X` a proper scheme over a field `k` of
dimension `≤ 1`, the classifying morphism `Spec k ⟶ Curves` factors through
`Curves⁺` if and only if `X ⟶ Spec k` is smooth except at finitely many
points. -/
@[stacks 0DZW]
theorem classifying_factorsThrough_isolatedSingularities_iff_finiteNonsmooth
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    isolatedSingularities (Spec (CommRingCat.of k))
        (mkOfSchemeOverField X hdim) ↔
      Set.Finite (setOf fun x : X.left ↦ ¬ X.hom.SmoothAt x) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
