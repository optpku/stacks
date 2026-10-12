/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.System.Basic

/-!
# Directed refinements and fixed-endpoint refinement morphisms

This file owns the two basic directed-refinement structures. It is independent
of fiber maps, request transport, and separation statements.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w r r' q

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

/-- A refinement of an inverse system to a nonempty directed essentially-small target inverse
system. The source-directed data is carried in the result, rather than required as a nonempty
input, because the source statements of Lemmas 7.39.1 and 7.39.2 derive nonemptiness from their
fiber elements. -/
structure DirectedRefinement
    {C : Type u} [Category.{v} C] {ι : Type w} [Preorder ι]
    (S : ιᵒᵖ ⥤ C) where
  /-- The source index is nonempty. -/
  sourceNonempty : Nonempty ι
  /-- The source index is directed. -/
  sourceDirected : IsDirected ι (· ≤ ·)
  /-- The source index is essentially small in the fiber universe. -/
  sourceEssentiallySmall : EssentiallySmall.{q} ιᵒᵖ
  /-- The directed target inverse system. -/
  target : DirectedInverseSystem.{u, v, r, q} C
  /-- The order embedding from the source index into the target index. -/
  embedding : ι ↪o target.index
  /-- The source system is the restriction of the target system along `embedding`. -/
  restrictionIso : S ≅ (embedding.toOrderHom.toFunctor).op ⋙ target.diagram

namespace DirectedRefinement

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [Preorder ι] {S : ιᵒᵖ ⥤ C}

/-- Directed refinements are determined by their target system, embedding, and restriction
isomorphism; the source nonemptiness, directedness, and smallness fields are proof-valued. -/
@[ext]
theorem ext {R Q : DirectedRefinement.{u, v, w, r, q} S}
    (h_target : R.target = Q.target) (h_embedding : HEq R.embedding Q.embedding)
    (h_restrictionIso : HEq R.restrictionIso Q.restrictionIso) :
    R = Q := sorry

end DirectedRefinement

namespace DirectedInverseSystem

variable {C : Type u} [Category.{v} C]
variable {X : DirectedInverseSystem.{u, v, r, q} C}
variable {Y : DirectedInverseSystem.{u, v, r', q} C}

/-- A refinement morphism with fixed source and target directed inverse systems. This packages the
order embedding and the comparison isomorphism without exposing an equality of dependent target
fields. -/
structure RefinementHom
    (X : DirectedInverseSystem.{u, v, r, q} C)
    (Y : DirectedInverseSystem.{u, v, r', q} C) where
  /-- The order embedding of the source index into the target index. -/
  embedding : X.index ↪o Y.index
  /-- The source inverse system is the restriction of the target system. -/
  restrictionIso : X.diagram ≅ (embedding.toOrderHom.toFunctor).op ⋙ Y.diagram

namespace RefinementHom

/-- Fixed-endpoint refinement morphisms are determined by their order embedding and dependent
restriction isomorphism. -/
@[ext]
theorem ext {f g : RefinementHom X Y} (h_embedding : f.embedding = g.embedding)
    (h_restrictionIso : HEq f.restrictionIso g.restrictionIso) :
    f = g := sorry

end RefinementHom

end DirectedInverseSystem

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
