module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.ClosedImmersion
public import Mathlib.Topology.Sets.Closeds

/-!
# Closed substacks with prescribed points

Closed replete object properties determine literal restricted algebraic stacks.
Their inclusions define the underlying subsets of the ambient point space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids (toFunctor)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

namespace Substack

/-- The groupoid fibration obtained by restricting to a closed object property. -/
def closedCategory (X : GroupoidsOver S) (P : ObjectProperty X.total)
    (hP : IsClosed X P) : GroupoidsOver S :=
  category X P (by
    obtain ⟨h, _⟩ := hP.2
    exact h)

/-- The literal inclusion of the category of a closed object property. -/
def closedInclusion (X : GroupoidsOver S) (P : ObjectProperty X.total)
    (hP : IsClosed X P) : closedCategory X P hP ⟶ X :=
  inclusion X P (by
    obtain ⟨h, _⟩ := hP.2
    exact h)

/-- The category restricted to a closed object property is an algebraic stack. -/
instance instAlgebraicStack_closedCategory (X : GroupoidsOver S)
    (P : ObjectProperty X.total) (hP : IsClosed X P) :
    AlgebraicStack (closedCategory X P hP) := by
  obtain ⟨h, hA, _⟩ := hP.2
  exact hA

/-- The inclusion of a closed object property is a closed immersion. -/
instance instClosedImmersion_closedInclusion (X : GroupoidsOver S)
    (P : ObjectProperty X.total) (hP : IsClosed X P) :
    ClosedImmersion (closedInclusion X P hP) := by
  obtain ⟨h, _, hI⟩ := hP.2
  exact hI

/-- The essential image of the literal inclusion of a closed object property
is that object property. -/
theorem closedInclusion_essImage (X : GroupoidsOver S) (P : ObjectProperty X.total)
    (hP : IsClosed X P) : (toFunctor (closedInclusion X P hP)).essImage = P :=
  sorry

/-- The underlying point-set of a closed object property is the range of its inclusion. -/
def pointsSet (X : GroupoidsOver S) [AlgebraicStack X] (P : ObjectProperty X.total)
    (hP : IsClosed X P) : Set (Points X) :=
  Set.range (Points.map (closedInclusion X P hP))

/-- Passing from a closed immersion to its essential-image substack preserves
its range on points. -/
theorem pointsSet_essImage {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y] (i : Y ⟶ X) [ClosedImmersion i] :
    pointsSet X (toFunctor i).essImage (image_isClosed i) =
      Set.range (Points.map i) :=
  sorry

end Substack

variable {X : GroupoidsOver S} [AlgebraicStack X]

/-- A structure on a closed subset of the point space is a closed replete
object property with exactly that underlying point-set. -/
def ClosedSubstackStructure (Z : Closeds (Points X)) :=
  {P : ObjectProperty X.total // ∃ hP : Substack.IsClosed X P,
    Substack.pointsSet X P hP = Z.carrier}

namespace ClosedSubstackStructure

variable {Z : Closeds (Points X)}

/-- A closed object property with a prescribed point-set gives a structure on that set. -/
def ofProperty (P : ObjectProperty X.total) (hP : Substack.IsClosed X P)
    (hZ : Substack.pointsSet X P hP = Z.carrier) : ClosedSubstackStructure Z :=
  ⟨P, hP, hZ⟩

/-- The underlying stack of a structure is the literal restricted category. -/
abbrev Y (T : ClosedSubstackStructure Z) : GroupoidsOver S :=
  Substack.closedCategory X T.val (by
    obtain ⟨hP, _⟩ := T.property
    exact hP)

/-- The inclusion of a structure is the literal full-subcategory inclusion. -/
abbrev ι (T : ClosedSubstackStructure Z) : T.Y ⟶ X :=
  Substack.closedInclusion X T.val (by
    obtain ⟨hP, _⟩ := T.property
    exact hP)

/-- A structure includes by a closed immersion whose range is the prescribed point-set. -/
theorem spec (T : ClosedSubstackStructure Z) :
    ClosedImmersion T.ι ∧ Set.range (Points.map T.ι) = Z.carrier := by
  refine ⟨inferInstance, ?_⟩
  obtain ⟨hP, hZ⟩ := T.property
  exact hZ

end ClosedSubstackStructure

end AlgebraicGeometry.AlgebraicStack
