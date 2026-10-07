module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Flat
public import ReasLib.Topology.ConnectedComponents.Set

/-!
# Canonical scheme structures on connected components

Each connected component of a scheme has unique ideal-sheaf data whose associated closed
immersion is flat and whose support is the given component.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A connected component of a scheme supports a unique ideal-sheaf datum whose associated
closed immersion is flat. -/
theorem existsUnique_flatIdealSheafData_connectedComponent
    (X : Scheme.{u}) (C : ConnectedComponents X) :
    ∃! I : X.IdealSheafData,
      Flat I.subschemeι ∧ (I.support : Set X) = C.set := sorry

end AlgebraicGeometry.Scheme
