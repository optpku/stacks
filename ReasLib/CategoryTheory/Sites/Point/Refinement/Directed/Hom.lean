module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Directed.Hom.Fixed

/-!
# Bundled morphisms of directed refinements

This file owns identity and composition of bundled directed refinements,
together with their source-system reconstruction, fixed-endpoint bridge,
fiber maps, and computation rules. Fixed-endpoint operations live in
`Directed.Hom.Fixed`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v w r r' r'' r''' q

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered

namespace DirectedRefinement

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} [Preorder ι] {S : ιᵒᵖ ⥤ C}

/-- The identity directed refinement of a directed inverse system. -/
noncomputable def id (T : DirectedInverseSystem.{u, v, r, q} C) :
    DirectedRefinement.{u, v, r, r, q} T.diagram where
  sourceNonempty := T.nonempty
  sourceDirected := T.directed
  sourceEssentiallySmall := T.fiberEssentiallySmall
  target := T
  embedding := OrderEmbedding.id T.index
  restrictionIso := (Functor.leftUnitor T.diagram).symm

/-- The identity directed refinement retains its system as target. -/
@[simp]
theorem id.target (T : DirectedInverseSystem.{u, v, r, q} C) :
    (id T).target = T := sorry

/-- The identity directed refinement uses the identity order embedding. -/
@[simp]
theorem id.embedding (T : DirectedInverseSystem.{u, v, r, q} C) :
    (id T).embedding = OrderEmbedding.id T.index := sorry

/-- Compose two directed refinements without exposing their smallness implementation details. -/
noncomputable def comp
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram) :
    DirectedRefinement.{u, v, w, r', q} S where
  sourceNonempty := R.sourceNonempty
  sourceDirected := R.sourceDirected
  sourceEssentiallySmall := R.sourceEssentiallySmall
  target := Q.target
  embedding := R.embedding.comp Q.embedding
  restrictionIso := Reindexing.OrderEmbedding.compIso R.embedding Q.embedding
    R.restrictionIso Q.restrictionIso

/-- A composite directed refinement has the target of its second factor. -/
@[simp]
theorem comp.target
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram) :
    (R.comp Q).target = Q.target := sorry

/-- The embedding of a composite directed refinement is the composite of its
embeddings. -/
@[simp]
theorem comp.embedding
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram) :
    (R.comp Q).embedding = R.embedding.comp Q.embedding := sorry

/-- The restriction isomorphism of a composite directed refinement is the
canonical composite reindexing isomorphism. -/
@[simp]
theorem comp.restrictionIso
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram) :
    (R.comp Q).restrictionIso =
      Reindexing.OrderEmbedding.compIso R.embedding Q.embedding
        R.restrictionIso Q.restrictionIso := sorry

/-- The source directed inverse system reconstructed from a directed refinement. This is the
canonical owner of the source nonemptiness, directedness, and smallness data. -/
noncomputable def sourceSystem
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    DirectedInverseSystem.{u, v, w, q} C where
  index := Preord.of ι
  nonempty := R.sourceNonempty
  directed := R.sourceDirected
  diagram := S
  fiberEssentiallySmall := R.sourceEssentiallySmall

/-- The reconstructed source system has the original source index. -/
@[simp]
theorem sourceSystem.index
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.sourceSystem.index = Preord.of ι := sorry

/-- The reconstructed source system retains the original source diagram. -/
@[simp]
theorem sourceSystem.diagram
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.sourceSystem.diagram = S := sorry

/-- Left composition by the identity directed refinement leaves a refinement
unchanged. -/
@[simp]
theorem id_comp (R : DirectedRefinement.{u, v, w, r, q} S) :
    (id R.sourceSystem).comp R = R := sorry

/-- Right composition by the identity directed refinement leaves a refinement
unchanged. -/
@[simp]
theorem comp_id (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.comp (id R.target) = R := sorry

/-- Composition of directed refinements is associative. -/
theorem comp_assoc
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram)
    (P : DirectedRefinement.{u, v, r', r'', q} Q.target.diagram) :
    (R.comp Q).comp P = R.comp (Q.comp P) := sorry

/-- The fixed-endpoint refinement morphism represented by a directed refinement. This bridges the
source-data packaging to `DirectedInverseSystem.RefinementHom`. -/
noncomputable def toRefinementHom
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    DirectedInverseSystem.RefinementHom R.sourceSystem R.target where
  embedding := R.embedding
  restrictionIso := R.restrictionIso

/-- Passing to the fixed-endpoint interface preserves the refinement
embedding. -/
@[simp]
theorem toRefinementHom.embedding
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.toRefinementHom.embedding = R.embedding := sorry

/-- Passing to the fixed-endpoint interface preserves the restriction
isomorphism. -/
@[simp]
theorem toRefinementHom.restrictionIso
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.toRefinementHom.restrictionIso = R.restrictionIso := sorry

/-- Reconstructing the source system of the fixed-endpoint bridge recovers the
original source system. -/
@[simp]
theorem DirectedInverseSystem.RefinementHom.toDirected.sourceSystem
    {X : DirectedInverseSystem.{u, v, w, q} C}
    {Y : DirectedInverseSystem.{u, v, r, q} C}
    (f : DirectedInverseSystem.RefinementHom X Y) :
    f.toDirected.sourceSystem = X := sorry

/-- Passing a directed refinement through the fixed-endpoint interface and
back recovers the original refinement. -/
@[simp]
theorem toRefinementHom.toDirected
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.toRefinementHom.toDirected = R := sorry

/-- The object fiber of the source system, using the smallness data stored in a directed
refinement. -/
noncomputable def sourceFiber [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    C ⥤ Type q :=
  R.sourceSystem.fiber

/-- The object-fiber map induced by a directed refinement. -/
noncomputable def fiberMap [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.sourceFiber ⟶ R.target.fiber :=
  R.toRefinementHom.fiberMap

/-- The fixed-endpoint bridge induces the same object-fiber map as the bundled
directed refinement. -/
@[simp]
theorem toRefinementHom.fiberMap [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S) :
    R.toRefinementHom.fiberMap = R.fiberMap := sorry

/-- The fiber map of the identity refinement is the identity. -/
@[simp]
theorem id.fiberMap [LocallySmall.{q} C]
    (T : DirectedInverseSystem.{u, v, r, q} C) :
    (id T).fiberMap = 𝟙 T.fiber := sorry

/-- The fiber map of a composite directed refinement is the composite of its fiber maps. -/
@[simp]
theorem comp.fiberMap [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    (Q : DirectedRefinement.{u, v, r, r', q} R.target.diagram) :
    (R.comp Q).fiberMap = R.fiberMap ≫ Q.fiberMap := sorry

/-- A canonical source-fiber generator for a directed refinement. -/
noncomputable def sourceMk [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    R.sourceFiber.obj W :=
  R.sourceSystem.fiberMk f

/-- The refinement map transports canonical source-fiber generators to target-fiber generators. -/
@[simp]
theorem fiberMap.sourceMk [LocallySmall.{q} C]
    (R : DirectedRefinement.{u, v, w, r, q} S)
    {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    R.fiberMap.app W (R.sourceMk f) =
      R.target.fiberMk (R.restrictionIso.inv.app U ≫ f) := sorry

/- Data audit: `sourceSystem` and `toRefinementHom` expose their index,
diagram, embedding, and restriction-isomorphism data explicitly. Any `sorryAx`
is confined to extensionality, unit, associativity, and fiber-map computation
proofs. -/

end DirectedRefinement

end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
