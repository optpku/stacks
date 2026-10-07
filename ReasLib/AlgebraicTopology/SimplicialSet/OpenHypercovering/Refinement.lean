module

public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Definition

/-!
# Refinements of open hypercoverings

A selected refinement consists of a simplicial map from the finer index set to the coarser one,
together with the corresponding pointwise inclusions of opens.  This module owns composition, the
resulting category, and the forgetful index functor.  Keeping this structure outside the core
definition module makes the category instance opt-in for consumers that use refinements.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace SSet.OpenHypercovering

variable {X : Type u} [TopologicalSpace X]

/-- A selected refinement of open hypercoverings.  The source `K` is the finer hypercovering and
the target `H` is the coarser one. -/
@[stacks 01H1 "selected open-hypercovering refinement"]
structure Refinement (K H : OpenHypercovering.{u, v} X) where
  /-- The simplicial map selecting the coarse index attached to each fine index. -/
  indexMap : K.I ⟶ H.I
  /-- The open attached to a fine index is contained in the selected coarse open. -/
  le {Delta : SimplexCategoryᵒᵖ} (i : K.I.obj Delta) :
    K.family.openAt i ≤ H.family.openAt (indexMap.app Delta i)

/-- Selected refinements are determined by their simplicial index map; the inclusion proofs are
proposition-valued fields. -/
@[ext, stacks 01H1 "selected refinement extensionality"]
theorem Refinement.ext {K H : OpenHypercovering.{u, v} X}
    {r s : Refinement K H} (h : r.indexMap = s.indexMap) : r = s := sorry

/-- Build a selected refinement from its simplicial index map and componentwise inclusions. -/
@[stacks 01H1 "open-hypercovering refinement constructor"]
def Refinement.ofIndexMap {K H : OpenHypercovering.{u, v} X}
    (indexMap : K.I ⟶ H.I)
    (h : ∀ ⦃Delta : SimplexCategoryᵒᵖ⦄ (i : K.I.obj Delta),
      K.family.openAt i ≤ H.family.openAt (indexMap.app Delta i)) :
    Refinement K H where
  indexMap := indexMap
  le := fun {Delta} i => h (Delta := Delta) i

/-- The inclusion required by the identity selected refinement. -/
@[stacks 01H1 "identity open-hypercovering refinement inclusion"]
theorem Refinement.id_le (H : OpenHypercovering.{u, v} X)
    {Delta : SimplexCategoryᵒᵖ} (i : H.I.obj Delta) :
    H.family.openAt i ≤ H.family.openAt i := sorry

/-- The identity selected refinement. -/
@[stacks 01H1 "identity open-hypercovering refinement"]
def Refinement.id (H : OpenHypercovering.{u, v} X) : Refinement H H where
  indexMap := 𝟙 H.I
  le := Refinement.id_le H

/-- The inclusion required by a composite selected refinement. -/
@[stacks 01H1 "composite open-hypercovering refinement inclusion"]
theorem Refinement.comp_le {H K L : OpenHypercovering.{u, v} X}
    (r : Refinement H K) (s : Refinement K L)
    {Delta : SimplexCategoryᵒᵖ} (i : H.I.obj Delta) :
    H.family.openAt i ≤
      L.family.openAt ((r.indexMap ≫ s.indexMap).app Delta i) := sorry

/-- Compose selected open-hypercovering refinements. -/
@[stacks 01H1 "composition of selected open-hypercovering refinements"]
def Refinement.comp {H K L : OpenHypercovering.{u, v} X}
    (r : Refinement H K) (s : Refinement K L) : Refinement H L where
  indexMap := r.indexMap ≫ s.indexMap
  le := r.comp_le s

/-- The index map of the identity selected refinement is the identity simplicial map. -/
@[simp, stacks 01H1 "identity refinement index map"]
theorem Refinement.id_indexMap (H : OpenHypercovering.{u, v} X) :
    (Refinement.id H).indexMap = 𝟙 H.I := sorry

/-- The index map of a composite selected refinement is the composite simplicial map. -/
@[simp, stacks 01H1 "composite refinement index map"]
theorem Refinement.comp_indexMap {H K L : OpenHypercovering.{u, v} X}
    (r : Refinement H K) (s : Refinement K L) :
    (r.comp s).indexMap = r.indexMap ≫ s.indexMap := sorry

/-- Identity selected refinement is a left identity for composition. -/
@[stacks 01H1 "left identity for open-hypercovering refinements"]
theorem Refinement.id_comp {H K : OpenHypercovering.{u, v} X}
    (r : Refinement H K) : (Refinement.id H).comp r = r := sorry

/-- Identity selected refinement is a right identity for composition. -/
@[stacks 01H1 "right identity for open-hypercovering refinements"]
theorem Refinement.comp_id {H K : OpenHypercovering.{u, v} X}
    (r : Refinement H K) : r.comp (Refinement.id K) = r := sorry

/-- Composition of selected open-hypercovering refinements is associative. -/
@[stacks 01H1 "associativity of open-hypercovering refinements"]
theorem Refinement.assoc {H K L M : OpenHypercovering.{u, v} X}
    (r : Refinement H K) (s : Refinement K L) (t : Refinement L M) :
    (r.comp s).comp t = r.comp (s.comp t) := sorry

/-- Open hypercoverings with selected refinements form the raw category of indexed open-cover
data.  Its arrows remember the chosen simplicial index map. -/
@[stacks 01H1 "category of selected open-hypercovering refinements"]
instance instCategory : Category (OpenHypercovering.{u, v} X) where
  Hom := Refinement
  id := Refinement.id
  comp := Refinement.comp
  id_comp := Refinement.id_comp
  comp_id := Refinement.comp_id
  assoc := Refinement.assoc

/-- The index simplicial set underlying an open hypercovering, functorial for selected
refinements. -/
@[stacks 01H1 "index functor for selected open-hypercovering refinements"]
def index : OpenHypercovering.{u, v} X ⥤ SSet.{v} where
  obj H := H.I
  map r := r.indexMap
  map_id := sorry
  map_comp := sorry

/-- The index functor returns the underlying simplicial index set on objects. -/
@[simp, stacks 01H1 "open-hypercovering index functor on objects"]
theorem index_obj (H : OpenHypercovering.{u, v} X) :
    (index (X := X)).obj H = H.I := sorry

/-- The index functor returns the selected simplicial index map on morphisms. -/
@[simp, stacks 01H1 "open-hypercovering index functor on morphisms"]
theorem index_map {H K : OpenHypercovering.{u, v} X} (r : H ⟶ K) :
    (index (X := X)).map r = r.indexMap := sorry

namespace Refinement.indexMap

/-- The component of the identity refinement is the identity function on each index type. -/
@[simp, stacks 01H1 "identity refinement component"]
theorem id_app (H : OpenHypercovering.{u, v} X)
    {Delta : SimplexCategoryᵒᵖ} (i : H.I.obj Delta) :
    ((𝟙 H : Refinement H H).indexMap.app Delta) i = i := sorry

/-- Components of a composite refinement are the composite of its selected index maps. -/
@[simp, stacks 01H1 "composite refinement component"]
theorem comp_app {H K L : OpenHypercovering.{u, v} X}
    (r : H ⟶ K) (s : K ⟶ L)
    {Delta : SimplexCategoryᵒᵖ} (i : H.I.obj Delta) :
    ((r ≫ s).indexMap.app Delta) i =
      s.indexMap.app Delta (r.indexMap.app Delta i) := sorry

end Refinement.indexMap

/-- `K.Refines H` means that the opens of `K` map into the opens of `H` along a simplicial
map of index sets.  Thus `K` is the finer open hypercovering. -/
@[stacks 01H1 "open-hypercovering refinement relation"]
def Refines (K H : OpenHypercovering.{u, v} X) : Prop :=
  ∃ f : K.I ⟶ H.I,
    ∀ ⦃Delta : SimplexCategoryᵒᵖ⦄ (i : K.I.obj Delta),
      K.family.openAt i ≤ H.family.openAt (f.app Delta i)

/-- `K.Restricts H` records the stronger refinement in which the open family of `K` is exactly
the restriction of the open family of `H` along a simplicial map. -/
@[stacks 01H1 "exact open-hypercovering restriction"]
def Restricts (K H : OpenHypercovering.{u, v} X) : Prop :=
  ∃ f : K.I ⟶ H.I, K.family = H.family.restrict f

/-- Exact restriction can be checked pointwise on the indexed opens. -/
@[stacks 01H1 "pointwise exact-restriction specification"]
theorem Restricts.iff_exists_openAt {K H : OpenHypercovering.{u, v} X} :
    K.Restricts H ↔
      ∃ f : K.I ⟶ H.I,
        ∀ ⦃Delta : SimplexCategoryᵒᵖ⦄ (i : K.I.obj Delta),
          K.family.openAt i = H.family.openAt (f.app Delta i) := sorry

/-- A selected refinement induces the corresponding inclusion-based refinement relation. -/
@[stacks 01H1 "selected refinement to refinement relation"]
theorem Refinement.refines {K H : OpenHypercovering.{u, v} X}
    (r : Refinement K H) : K.Refines H := sorry

/-- The refinement relation is equivalent to the existence of selected refinement data. -/
@[stacks 01H1 "refinement relation selected-data specification"]
theorem Refines.iff_nonempty {K H : OpenHypercovering.{u, v} X} :
    K.Refines H ↔ Nonempty (Refinement K H) := sorry

/-- Refinement is reflexive. -/
@[stacks 01H1 "reflexivity of open-hypercovering refinement"]
theorem Refines.refl (H : OpenHypercovering.{u, v} X) : H.Refines H := sorry

/-- Refinement of open hypercoverings is transitive. -/
@[stacks 01H1 "transitivity of open-hypercovering refinement"]
theorem Refines.trans {H K L : OpenHypercovering.{u, v} X}
    (hHK : H.Refines K) (hKL : K.Refines L) : H.Refines L := sorry

/-- Exact restrictions are refinements. -/
@[stacks 01H1 "exact restrictions are refinements"]
theorem Restricts.refines {K H : OpenHypercovering.{u, v} X}
    (h : K.Restricts H) : K.Refines H := sorry

/-- Exact restriction is reflexive. -/
@[stacks 01H1 "reflexivity of exact open-hypercovering restriction"]
theorem Restricts.refl (H : OpenHypercovering.{u, v} X) : H.Restricts H := sorry

/-- Exact restrictions compose. -/
@[stacks 01H1 "transitivity of exact open-hypercovering restriction"]
theorem Restricts.trans {H K L : OpenHypercovering.{u, v} X}
    (hHK : H.Restricts K) (hKL : K.Restricts L) : H.Restricts L := sorry

end SSet.OpenHypercovering
