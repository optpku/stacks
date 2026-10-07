module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Reduced induced closed substacks

A closed subset of the canonical space of points of an algebraic stack is the
underlying point-set of a unique reduced closed substack. Irreducible
components inherit that reduced induced structure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

namespace ClosedSubstack

/-- The underlying set of points of a closed substack, as the image of
`Points.map` along its inclusion. -/
def pointsSet (T : ClosedSubstack X) : Set (Points X) :=
  Set.range (Points.map T.ι)

/-- `pointsSet T` is the range of `Points.map T.ι`. -/
theorem pointsSet_eq (T : ClosedSubstack X) :
    T.pointsSet = Set.range (Points.map T.ι) :=
  sorry

/-- A point of `|X|` lies in `pointsSet T` if and only if it is the image of a
point of `|T.Y|`. -/
theorem mem_pointsSet (T : ClosedSubstack X) {x : Points X} :
    x ∈ T.pointsSet ↔ ∃ y : Points T.Y, Points.map T.ι y = x :=
  sorry

/-- The image `|T.Y| ⊆ |X|` is closed in any canonical topology on `|X|`. -/
theorem isClosed_pointsSet {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : ClosedSubstack X) :
    @IsClosed (Points X) τ T.pointsSet :=
  sorry

/-- A canonical closed subset of `|X|` is the point-set of some reduced closed
substack. -/
theorem exists_reduced {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (Z : @Closeds (Points X) τ) :
    ∃ T : ClosedSubstack X, T.pointsSet = Z.carrier ∧ IsReduced T.Y :=
  sorry

/-- The reduced induced closed substack structure on a canonical closed subset
of `|X|`. -/
def reduced {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (Z : @Closeds (Points X) τ) : ClosedSubstack X :=
  Classical.choose (exists_reduced hτ Z)

/-- The reduced induced structure on `Z` is a reduced closed substack with
point-set `Z`. -/
theorem reduced_spec {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (Z : @Closeds (Points X) τ) :
    (reduced hτ Z).pointsSet = Z.carrier ∧ IsReduced (reduced hτ Z).Y :=
  sorry

/-- A reduced closed substack with point-set `Z` admits a unique morphism over
`X` to the reduced induced structure. -/
theorem reduced_unique {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) {Z : @Closeds (Points X) τ}
    (T : ClosedSubstack X) (h_eq : T.pointsSet = Z.carrier)
    (h_reduced : IsReduced T.Y) :
    ∃! f : T.Y ⟶ (reduced hτ Z).Y, f ≫ (reduced hτ Z).ι = T.ι :=
  sorry

/-- The reduced induced closed substack on a canonical closed subset is
reduced. -/
instance instIsReduced_reduced {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (Z : @Closeds (Points X) τ) :
    IsReduced (reduced hτ Z).Y :=
  sorry

/-- The reduced induced closed substack of a locally Noetherian algebraic stack
is locally Noetherian. -/
instance instIsLocallyNoetherian_reduced {τ : TopologicalSpace (Points X)}
    [IsLocallyNoetherian X] (hτ : IsPointsTopology X τ)
    (Z : @Closeds (Points X) τ) : IsLocallyNoetherian (reduced hτ Z).Y :=
  sorry

/-- The unique point of a closed substack lying over a given point of its
image. -/
def preimagePoint (T : ClosedSubstack X) {x : Points X} (hx : x ∈ T.pointsSet) :
    Points T.Y :=
  Classical.choose hx

/-- `preimagePoint T hx` is sent to `x` by the map on points induced by `T.ι`. -/
theorem preimagePoint_map (T : ClosedSubstack X) {x : Points X}
    (hx : x ∈ T.pointsSet) :
    Points.map T.ι (preimagePoint T hx) = x :=
  sorry

end ClosedSubstack

/-- The closed subset of `|X|` carried by an irreducible component. -/
def irreducibleComponentClosed {τ : TopologicalSpace (Points X)}
    (T : @irreducibleComponents (Points X) τ) : @Closeds (Points X) τ where
  carrier := (T : Set (Points X))
  isClosed' :=
    @isClosed_of_mem_irreducibleComponents (Points X) τ (T : Set (Points X)) T.2

/-- Membership in `irreducibleComponentClosed T` agrees with membership in the
component `T`. -/
theorem mem_irreducibleComponentClosed {τ : TopologicalSpace (Points X)}
    (T : @irreducibleComponents (Points X) τ) {x : Points X} :
    x ∈ (irreducibleComponentClosed T).carrier ↔ x ∈ (T : Set (Points X)) :=
  sorry

/-- The reduced induced closed substack supported on an irreducible component of
`|X|`. -/
def irreducibleComponentSubstack {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ) :
    ClosedSubstack X :=
  ClosedSubstack.reduced hτ (irreducibleComponentClosed T)

/-- The reduced induced closed substack of an irreducible component is reduced. -/
instance instIsReduced_irreducibleComponentSubstack
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ)
    (T : @irreducibleComponents (Points X) τ) :
    IsReduced (irreducibleComponentSubstack hτ T).Y :=
  sorry

/-- The reduced induced closed substack of an irreducible component of a locally
Noetherian algebraic stack is locally Noetherian. -/
instance instIsLocallyNoetherian_irreducibleComponentSubstack
    {τ : TopologicalSpace (Points X)} [IsLocallyNoetherian X]
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ) :
    IsLocallyNoetherian (irreducibleComponentSubstack hτ T).Y :=
  sorry

/-- A point of an irreducible component of `|X|` lies on the point-set of the
corresponding reduced induced closed substack. -/
theorem mem_pointsSet_irreducibleComponentSubstack {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ)
    {x : Points X} (hx : x ∈ (T : Set (Points X))) :
    x ∈ (irreducibleComponentSubstack hτ T).pointsSet :=
  sorry

/-- The unique point of an irreducible-component closed substack lying over a
given point of the component. -/
def irreducibleComponentSubstack.point {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (T : @irreducibleComponents (Points X) τ)
    (x : Points X) (hx : x ∈ (T : Set (Points X))) :
    Points (irreducibleComponentSubstack hτ T).Y :=
  ClosedSubstack.preimagePoint (irreducibleComponentSubstack hτ T)
    (mem_pointsSet_irreducibleComponentSubstack hτ T hx)

end AlgebraicGeometry.AlgebraicStack
