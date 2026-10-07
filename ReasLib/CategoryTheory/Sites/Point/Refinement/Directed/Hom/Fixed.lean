module

public import ReasLib.CategoryTheory.Sites.Point.OrderedRefinement.EssentiallySmall.Fiber
public import ReasLib.CategoryTheory.Sites.Point.Reindexing.OrderEmbedding.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Directed.Basic

/-!
# Fixed-endpoint morphisms of directed inverse systems

This file owns identity, composition, ordered and bundled bridges, and
object-fiber maps for refinement morphisms with fixed directed-system
endpoints.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v r r' r'' r''' q

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

namespace DirectedInverseSystem

variable {C : Type u} [Category.{v} C]
variable {X : DirectedInverseSystem.{u, v, r, q} C}
variable {Y : DirectedInverseSystem.{u, v, r', q} C}
variable {Z : DirectedInverseSystem.{u, v, r'', q} C}
variable {W : DirectedInverseSystem.{u, v, r''', q} C}

namespace RefinementHom

/-- The identity refinement morphism of a directed inverse system. -/
noncomputable def id (X : DirectedInverseSystem.{u, v, r, q} C) :
    RefinementHom X X where
  embedding := OrderEmbedding.id X.index
  restrictionIso := Reindexing.OrderEmbedding.idIso X.diagram

/-- Composition of fixed-endpoint refinement morphisms. -/
noncomputable def comp (f : RefinementHom X Y) (g : RefinementHom Y Z) :
    RefinementHom X Z where
  embedding := f.embedding.comp g.embedding
  restrictionIso := Reindexing.OrderEmbedding.compIso f.embedding g.embedding
    f.restrictionIso g.restrictionIso

/-- Forget the directed-system endpoints of a fixed-endpoint refinement morphism, retaining the
pure order-embedding refinement data. -/
noncomputable def toOrdered (f : RefinementHom X Y) :
    OrderedRefinement X.diagram Y.diagram where
  embedding := f.embedding
  restrictionIso := f.restrictionIso

/-- Package an ordered refinement between the diagrams of two directed inverse
systems as a fixed-endpoint refinement morphism. -/
noncomputable def ofOrdered (R : OrderedRefinement X.diagram Y.diagram) :
    RefinementHom X Y where
  embedding := R.embedding
  restrictionIso := R.restrictionIso

/-- A fixed-endpoint refinement morphism gives the bundled directed-refinement interface. -/
noncomputable def toDirected (f : RefinementHom X Y) :
    DirectedRefinement.{u, v, r, r', q} X.diagram where
  sourceNonempty := X.nonempty
  sourceDirected := X.directed
  sourceEssentiallySmall := X.fiberEssentiallySmall
  target := Y
  embedding := f.embedding
  restrictionIso := f.restrictionIso

/-- Forgetting endpoints preserves the order embedding of a fixed-endpoint
refinement. -/
@[simp]
theorem toOrdered.embedding (f : RefinementHom X Y) :
    f.toOrdered.embedding = f.embedding := sorry

/-- Forgetting endpoints preserves the restriction isomorphism of a
fixed-endpoint refinement. -/
@[simp]
theorem toOrdered.restrictionIso (f : RefinementHom X Y) :
    f.toOrdered.restrictionIso = f.restrictionIso := sorry

/-- Forgetting the endpoints of a packaged ordered refinement recovers the
original ordered refinement. -/
@[simp]
theorem ofOrdered.toOrdered (R : OrderedRefinement X.diagram Y.diagram) :
    (ofOrdered R).toOrdered = R := sorry

/-- Repackaging the ordered refinement underlying a fixed-endpoint morphism
recovers the original morphism. -/
@[simp]
theorem toOrdered.ofOrdered (f : RefinementHom X Y) :
    ofOrdered f.toOrdered = f := sorry

/-- The directed-refinement bridge has the prescribed target system. -/
@[simp]
theorem toDirected.target (f : RefinementHom X Y) :
    f.toDirected.target = Y := sorry

/-- The directed-refinement bridge preserves the order embedding. -/
@[simp]
theorem toDirected.embedding (f : RefinementHom X Y) :
    f.toDirected.embedding = f.embedding := sorry

/-- The directed-refinement bridge preserves the restriction isomorphism. -/
@[simp]
theorem toDirected.restrictionIso (f : RefinementHom X Y) :
    f.toDirected.restrictionIso = f.restrictionIso := sorry

/-- The object-fiber map induced by a fixed-endpoint refinement morphism. -/
noncomputable def fiberMap [LocallySmall.{q} C] (f : RefinementHom X Y) :
    X.fiber ⟶ Y.fiber :=
  OrderedRefinement.EssentiallySmall.fiberMap f.toOrdered

/-- A fixed-endpoint refinement sends a canonical source-fiber generator to
the corresponding target-fiber generator. -/
@[simp]
theorem fiberMap.fiberMk [LocallySmall.{q} C] (f : RefinementHom X Y)
    {U : X.indexᵒᵖ} {A : C} (g : X.diagram.obj U ⟶ A) :
    f.fiberMap.app A (X.fiberMk g) =
      Y.fiberMk (f.restrictionIso.inv.app U ≫ g) := sorry

/-- The embedding of the identity refinement is the identity order embedding. -/
@[simp]
theorem id.embedding (X : DirectedInverseSystem.{u, v, r, q} C) :
    (id X).embedding = OrderEmbedding.id X.index := sorry

/-- The embedding of a composite refinement is the composite of embeddings. -/
@[simp]
theorem comp.embedding (f : RefinementHom X Y) (g : RefinementHom Y Z) :
    (f.comp g).embedding = f.embedding.comp g.embedding := sorry

/-- Left composition by the identity refinement leaves a fixed-endpoint refinement unchanged. -/
@[simp]
theorem id_comp (f : RefinementHom X Y) : (id X).comp f = f := sorry

/-- Right composition by the identity refinement leaves a fixed-endpoint refinement unchanged. -/
@[simp]
theorem comp_id (f : RefinementHom X Y) : f.comp (id Y) = f := sorry

/-- Composition of fixed-endpoint refinement morphisms is associative. -/
theorem comp_assoc (f : RefinementHom X Y) (g : RefinementHom Y Z)
    (h : RefinementHom Z W) :
    (f.comp g).comp h = f.comp (g.comp h) := sorry

/-- The fiber map of the identity fixed-endpoint refinement is the identity. -/
@[simp]
theorem id.fiberMap [LocallySmall.{q} C]
    (X : DirectedInverseSystem.{u, v, r, q} C) :
    (id X).fiberMap = 𝟙 X.fiber := sorry

/-- The fiber map of a composite fixed-endpoint refinement is the composite of its fiber maps. -/
@[simp]
theorem comp.fiberMap [LocallySmall.{q} C]
    (f : RefinementHom X Y) (g : RefinementHom Y Z) :
    (f.comp g).fiberMap = f.fiberMap ≫ g.fiberMap := sorry

end RefinementHom

end DirectedInverseSystem

/- Data audit: `toOrdered` exposes its embedding and restriction-isomorphism
data explicitly; proof debt is confined to the theorem API. -/

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
