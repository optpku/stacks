module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.RelatedPoints
import StacksCheckRecall

/-!
# Related-point classes

If `π : Y ⟶ f.simplicialScheme` is cartesian, then the sets `relatedPoints y`
are equivalence classes of points of `Y _⦋0⦌`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicGeometry

/- Lemma 85.31.1 (1): every degree-zero point belongs to its related-point class.
The generalized reflexivity theorem applies to every simplicial scheme, in particular to
the cartesian simplicial scheme over the Čech nerve in the statement. -/
@[stacks 024G] #check (AlgebraicGeometry.self_mem_relatedPoints :
  ∀ {Y : SimplicialObject Scheme.{u}} (y : Y _⦋0⦌), y ∈ relatedPoints y)

/- Lemma 85.31.1 (2): if `π : Y ⟶ f.simplicialScheme` is a cartesian morphism of
simplicial schemes, then for points `y`, `y'` of `Y _⦋0⦌` a nonempty intersection
`relatedPoints y ∩ relatedPoints y'` implies `relatedPoints y = relatedPoints y'`. -/
@[stacks 024G] #check (AlgebraicGeometry.relatedPoints_eq_of_inter_nonempty :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π] (y y' : Y _⦋0⦌),
    (relatedPoints y ∩ relatedPoints y').Nonempty → relatedPoints y = relatedPoints y')

#check (AlgebraicGeometry.relatedPoints_equivalence :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    (Y : SimplicialObject Scheme.{u}) (π : Y ⟶ f.simplicialScheme)
    [SimplicialObject.IsCartesian π],
    Equivalence (fun y y' : Y _⦋0⦌ ↦ y' ∈ relatedPoints y))

end AlgebraicGeometry
