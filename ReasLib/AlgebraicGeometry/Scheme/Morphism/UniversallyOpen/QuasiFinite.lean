module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite type, locally quasi-finite morphism to a locally Noetherian,
geometrically unibranch scheme is universally open if every irreducible component
of the source dominates an irreducible component of the target. -/
@[stacks 0F32]
theorem universallyOpen_of_dominantComponents {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian Y]
    (hY : Y.isGeometricallyUnibranch)
    (h_components : ∀ C : irreducibleComponents X, ∃ D : irreducibleComponents Y,
      closure (Set.image f.base (C : Set X)) = (D : Set Y)) :
    UniversallyOpen f := sorry

end AlgebraicGeometry.Scheme.Hom
