module

public import Mathlib.Topology.LocallyClosed
public import ReasLib.Topology.LocallyClosed.Subsets
public import stacks_project.Chap100.Lemma_100_9_12_Opens
public import stacks_project.Chap100.Definition_100_10_4_Reduced
public import stacks_project.Chap100.Lemma_100_9_3

/-!
# Reduced induced algebraic stacks on locally closed subsets

A locally closed subset `T` of `Points X` determines an open substack `U` with
point-set `coborder T`, and then the reduced induced closed substack of `U` on
`T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The boundary of a locally closed subset of `Points X`, as `closure T \ T`. -/
def boundary (T : LocallyCloseds (Points X)) : Set (Points X) :=
  closure (T : Set (Points X)) \ (T : Set (Points X))

/-- The boundary is the complement of `T` in its closure. -/
theorem boundary_eq (T : LocallyCloseds (Points X)) :
    boundary T = closure (T : Set (Points X)) \ (T : Set (Points X)) :=
  sorry

/-- The coborder of `T` is the complement of the boundary. -/
theorem coborder_eq_compl_boundary (T : LocallyCloseds (Points X)) :
    coborder (T : Set (Points X)) = (boundary T)ᶜ :=
  sorry

/-- The open substack of `X` with underlying point-set `Points X \ boundary T`. -/
def ambientOpen (T : LocallyCloseds (Points X)) : OpenSubstack X :=
  OpenSubstack.ofOpens ⟨coborder (T : Set (Points X)), T.property.isOpen_coborder⟩

/-- The inclusion of the ambient open is an open immersion. -/
instance instOpenImmersion_ambientOpen_ι (T : LocallyCloseds (Points X)) :
    OpenImmersion (ambientOpen T).ι :=
  (ambientOpen T).isOpenImmersion

/-- The underlying point-set of the ambient open is the coborder of `T`. -/
theorem ambientOpen_pointsSet (T : LocallyCloseds (Points X)) :
    (ambientOpen T).pointsSet = coborder (T : Set (Points X)) :=
  sorry

/-- The locally closed subset `T`, viewed as a closed subset of the ambient open. -/
def closedSubset (T : LocallyCloseds (Points X)) :
    Closeds (Points (ambientOpen T).Y) where
  carrier := Points.map (ambientOpen T).ι ⁻¹' (T : Set (Points X))
  isClosed' := sorry

/-- The closed subset is the inverse image of `T` under the ambient open inclusion
on points. -/
theorem coe_closedSubset (T : LocallyCloseds (Points X)) :
    (closedSubset T : Set (Points (ambientOpen T).Y)) =
      Points.map (ambientOpen T).ι ⁻¹' (T : Set (Points X)) :=
  sorry

/-- The reduced induced closed-substack structure on `T` inside the ambient open. -/
abbrev closedStructure (T : LocallyCloseds (Points X)) :
    ClosedSubstackStructure (closedSubset T) :=
  ClosedSubstackStructure.reduced (closedSubset T)

/-- The closed stage is the reduced induced structure on `closedSubset T`. -/
theorem closedStructure_eq (T : LocallyCloseds (Points X)) :
    closedStructure T = ClosedSubstackStructure.reduced (closedSubset T) :=
  sorry

/-- The reduced induced algebraic stack on a locally closed subset. -/
abbrev stack (T : LocallyCloseds (Points X)) : GroupoidsOver S :=
  (closedStructure T).Y

/-- The underlying stack of the locally closed reduction is the stack of the closed
stage. -/
theorem stack_eq (T : LocallyCloseds (Points X)) :
    stack T = (closedStructure T).Y :=
  sorry

/-- The closed immersion into the ambient open substack. -/
abbrev ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    stack T ⟶ (ambientOpen T).Y :=
  (closedStructure T).ι

/-- The closed stage is a closed immersion. -/
instance instClosedImmersion_ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    ClosedImmersion (ιToAmbientOpen T) :=
  (closedStructure T).substack.isClosedImmersion

/-- The closed stage has image equal to the prescribed closed subset of the ambient
open. -/
theorem range_ιToAmbientOpen (T : LocallyCloseds (Points X)) :
    Set.range (Points.map (ιToAmbientOpen T)) = closedSubset T :=
  sorry

/-- The canonical immersion of the reduced induced stack into `X`. -/
abbrev ι (T : LocallyCloseds (Points X)) : stack T ⟶ X :=
  ιToAmbientOpen T ≫ (ambientOpen T).ι

/-- The canonical map of a locally closed induced stack is an immersion. -/
instance instImmersion_ι (T : LocallyCloseds (Points X)) :
    Immersion (ι T) :=
  Immersion.comp (ιToAmbientOpen T) (ambientOpen T).ι

/-- The canonical immersion presents a strictly full subcategory of `X`. -/
instance instIsStrictlyFull_ι (T : LocallyCloseds (Points X)) :
    IsStrictlyFull (ι T) :=
  sorry

/-- The canonical immersion has set-theoretic range exactly `T`. -/
theorem range_ι (T : LocallyCloseds (Points X)) :
    Set.range (Points.map (ι T)) = T :=
  sorry

/-- The reduced induced stack on `T` is obtained by a closed immersion into the
open complement of the boundary, hence an immersion into `X`, and is reduced with
point-set `T`. -/
theorem spec (T : LocallyCloseds (Points X)) :
    OpenImmersion (ambientOpen T).ι ∧
      ClosedImmersion (ιToAmbientOpen T) ∧
      Immersion (ι T) ∧
      IsReduced (stack T) ∧
      Set.range (Points.map (ι T)) = (T : Set (Points X)) :=
  sorry

/-- The reduced induced stack on `T`, as a locally closed substack of `X`. -/
def toLocallyClosedSubstack (T : LocallyCloseds (Points X)) :
    LocallyClosedSubstack X :=
  LocallyClosedSubstack.ofι (ι T)

/-- The inclusion of `toLocallyClosedSubstack T` is the canonical immersion. -/
theorem toLocallyClosedSubstack_ι (T : LocallyCloseds (Points X)) :
    (toLocallyClosedSubstack T).ι = ι T :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyClosedReduction

namespace AlgebraicGeometry.AlgebraicStack.LocallyClosedSubstack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The reduced induced substack structure on a locally closed subset of `Points X`. -/
def reduced (T : LocallyCloseds (Points X)) : LocallyClosedSubstack X :=
  LocallyClosedReduction.toLocallyClosedSubstack T

/-- The inclusion of the reduced induced substack structure is the canonical immersion. -/
theorem reduced_ι (T : LocallyCloseds (Points X)) :
    (reduced T).ι = LocallyClosedReduction.ι T :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyClosedSubstack
