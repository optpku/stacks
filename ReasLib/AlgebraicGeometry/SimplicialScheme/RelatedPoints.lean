module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicTopology.CechNerve
public import ReasLib.AlgebraicGeometry.SimplicialScheme.CechNerve
public import ReasLib.AlgebraicTopology.SimplicialObject.Cartesian

/-!
# Related points of a simplicial scheme
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicGeometry

/-- The set of degree-zero points related to `y` by a degree-one simplex. -/
def relatedPoints {Y : SimplicialObject Scheme.{u}} (y : Y _⦋0⦌) : Set (Y _⦋0⦌) :=
  (Y.δ (0 : Fin 2)) '' ((Y.δ (1 : Fin 2)) ⁻¹' {y})

/-- Membership in `relatedPoints y` is witnessed by a degree-one point with the two specified
face values. -/
theorem mem_relatedPoints {Y : SimplicialObject Scheme.{u}} {y y' : Y _⦋0⦌} :
    y' ∈ relatedPoints y ↔
      ∃ y1 : Y _⦋1⦌, Y.δ (1 : Fin 2) y1 = y ∧ Y.δ (0 : Fin 2) y1 = y' := sorry

/-- Every degree-zero point of a simplicial scheme is related to itself. -/
theorem self_mem_relatedPoints {Y : SimplicialObject Scheme.{u}} (y : Y _⦋0⦌) :
    y ∈ relatedPoints y := sorry

/-- The face-witness relation on degree-zero points of a simplicial scheme cartesian over
a Čech nerve is an equivalence relation. -/
theorem relatedPoints_equivalence {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π] :
    Equivalence (fun y y' : Y _⦋0⦌ ↦ y' ∈ relatedPoints y) := sorry

/-- Two related-point classes of a simplicial scheme cartesian over a Čech nerve are equal
if their intersection is nonempty. -/
theorem relatedPoints_eq_of_inter_nonempty {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π] (y y' : Y _⦋0⦌) :
    (relatedPoints y ∩ relatedPoints y').Nonempty → relatedPoints y = relatedPoints y' := sorry

/-- For a quasi-compact morphism, the degree-zero points related to any point of a cartesian
Čech simplicial scheme form a compact subset. -/
theorem isCompact_relatedPoints {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (Y : SimplicialObject Scheme.{u})
    (π : Y ⟶ (CategoryTheory.Arrow.mk f).cechNerve)
    [SimplicialObject.IsCartesian π] (y : Y _⦋0⦌) :
    IsCompact (relatedPoints y) := sorry

end AlgebraicGeometry
