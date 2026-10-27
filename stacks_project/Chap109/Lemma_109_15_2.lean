/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.LocalCompleteIntersection.IsolatedSingularities
import StacksCheckRecall

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

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.15.2 (1): the structure morphism of the local complete intersection
curves with isolated singularities is smooth. -/
@[stacks 0DZX] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instSmooth_lciPlus :
  ∀ (S : Scheme.{u}), CohStack.Hom.Smooth
    (inclusionOf (lciPlus S) ≫ CohStack.toIdentitySlice (toGroupoids S)))

/- Lemma 109.15.2 (2): a family is classified by the intersection locus precisely
when it is a local complete intersection and its singular locus with any/some
closed subspace structure is finite over the base. -/
@[stacks 0DZX] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_lciPlus_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    lciPlus S P ↔
      AlgebraicSpace.IsLocalCompleteIntersection (hom P) ∧
        ∀ T : ClosedSubspaceStructure (nonsmoothLocusClosed (hom P)),
          IsFinite (T.ι ≫ hom P))

/- Lemma 109.15.2 (3): a proper scheme of dimension at most one over a field is
classified by the intersection locus precisely when it is a local complete
intersection over the field and smooth except at finitely many points. -/
@[stacks 0DZX] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_lciPlus_iff_scheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    lciPlus (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      IsLocalCompleteIntersectionOver k X.hom ∧
        Set.Finite (setOf fun x : X.left ↦ ¬ X.hom.SmoothAt x))

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
