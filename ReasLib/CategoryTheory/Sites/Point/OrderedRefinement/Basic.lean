module

public import ReasLib.CategoryTheory.Sites.Point.Reindexing.OrderEmbedding.Basic

/-!
# Ordered refinements of inverse systems

This module owns pure order-embedding refinement data, its identity and
composition operations, and factorization coherence.  It is independent of
fiber smallness and colimit assumptions.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w₀ w₁ w₂ w₃

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

variable {C : Type u} [Category.{v} C]

/-- A pure refinement of inverse systems indexed by preorders.  Unlike a
`DirectedRefinement`, this data does not impose nonemptiness, directedness, or
smallness conditions on either index. -/
@[stacks 00YP "ordered inverse-system refinement"]
structure OrderedRefinement
    {ι : Type w₀} [Preorder ι] {ι' : Type w₁} [Preorder ι']
    (S : ιᵒᵖ ⥤ C) (T : ι'ᵒᵖ ⥤ C) where
  /-- The order embedding from the source index to the target index. -/
  embedding : ι ↪o ι'
  /-- The source inverse system is the restriction of the target system along
  the stored embedding. -/
  restrictionIso : S ≅ (embedding.toOrderHom.toFunctor).op ⋙ T

namespace OrderedRefinement

variable {ι : Type w₀} [Preorder ι]
variable {ι' : Type w₁} [Preorder ι']
variable {ι'' : Type w₂} [Preorder ι'']
variable {S : ιᵒᵖ ⥤ C} {T : ι'ᵒᵖ ⥤ C} {U : ι''ᵒᵖ ⥤ C}

/-- Ordered refinements are determined by their order embedding and dependent restriction
isomorphism. -/
@[ext]
theorem ext {R Q : OrderedRefinement S T} (h_embedding : R.embedding = Q.embedding)
    (h_restrictionIso : HEq R.restrictionIso Q.restrictionIso) :
    R = Q := sorry

/-- Build a pure refinement from an order embedding and its restriction
isomorphism.  This is the canonical constructor for APIs whose source-facing
data is presented as `(j, T, e)`. -/
def ofEmbedding (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C)
    (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T) : OrderedRefinement S T where
  embedding := j
  restrictionIso := e

/-- The identity pure refinement of an inverse system. -/
noncomputable def id (S : ιᵒᵖ ⥤ C) : OrderedRefinement S S where
  embedding := OrderEmbedding.id ι
  restrictionIso := Reindexing.OrderEmbedding.idIso S

/-- Composition of pure order-embedding refinements. -/
noncomputable def comp (R : OrderedRefinement S T) (Q : OrderedRefinement T U) :
    OrderedRefinement S U where
  embedding := R.embedding.comp Q.embedding
  restrictionIso := Reindexing.OrderEmbedding.compIso R.embedding Q.embedding
    R.restrictionIso Q.restrictionIso

/-- `P` is the refinement obtained by first applying `R` and then `Q`.

This records equality of the order embedding and of the induced inverse-system identification
without committing clients to a particular construction of `P`.  It is the reusable coherence
predicate for diagrams of refinements over one fixed source inverse system. -/
@[stacks 00YP "ordered refinement factorization"]
def IsFactorization (R : OrderedRefinement S T) (Q : OrderedRefinement T U)
    (P : OrderedRefinement S U) : Prop :=
  P.embedding = R.embedding.comp Q.embedding ∧
    HEq P.restrictionIso
      (Reindexing.OrderEmbedding.compIso R.embedding Q.embedding
        R.restrictionIso Q.restrictionIso)

namespace IsFactorization

/-- The canonical composite refinement has its expected factorization coherence. -/
theorem comp (R : OrderedRefinement S T) (Q : OrderedRefinement T U) :
    IsFactorization R Q (R.comp Q) := sorry

/-- Factoring through the identity refinement on the source is canonical. -/
theorem id_left (R : OrderedRefinement S T) :
    IsFactorization (id S) R R := sorry

/-- Factoring through the identity refinement on the target is canonical. -/
theorem id_right (R : OrderedRefinement S T) :
    IsFactorization R (id T) R := sorry

/-- Factorization is closed under a further refinement of its target.

This is the transitivity rule for coherence diagrams of refinements: if `P` factors as `R`
followed by `Q`, and `W` factors as `P` followed by `H`, then `W` factors as `R` followed by
the composite `Q.comp H`. -/
theorem trans
    {ι''' : Type w₃} [Preorder ι'''] {V : ι'''ᵒᵖ ⥤ C}
    {R : OrderedRefinement S T} {Q : OrderedRefinement T U}
    {P : OrderedRefinement S U} {H : OrderedRefinement U V}
    {W : OrderedRefinement S V}
    (hRQ : IsFactorization R Q P) (hPH : IsFactorization P H W) :
    IsFactorization R (Q.comp H) W := sorry

end IsFactorization

end OrderedRefinement

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
