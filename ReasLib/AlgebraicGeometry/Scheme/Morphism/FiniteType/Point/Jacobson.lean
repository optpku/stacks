module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point.Topology

/-!
# Jacobson schemes and finite-type points

This file characterizes Jacobson schemes through their finite-type points and through the behavior
of closed points under locally finite type morphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is Jacobson exactly when its finite-type points are its closed points, equivalently
when every locally finite type morphism to it maps closed points to closed points, with finite
residue-field extension at each such point. -/
theorem jacobsonSpace_tfae_finiteTypePoints (S : Scheme.{u}) :
    List.TFAE
      [ JacobsonSpace S
      , finiteTypePoints S = closedPoints S
      , ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f],
          Set.MapsTo f (closedPoints T) (closedPoints S)
      , ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f], ∀ t : T,
          t ∈ closedPoints T →
            f t ∈ closedPoints S ∧
              Module.Finite (S.residueField (f t)) (T.residueField t)
      ] := sorry

/-- A scheme is Jacobson if and only if its finite-type points are exactly its closed points. -/
theorem jacobsonSpace_iff_finiteTypePoints_eq_closedPoints (S : Scheme.{u}) :
    JacobsonSpace S ↔ finiteTypePoints S = closedPoints S := sorry

/-- A scheme is Jacobson if and only if every locally finite type morphism to it maps closed
points to closed points. -/
theorem jacobsonSpace_iff_mapsTo_closedPoints_of_locallyOfFiniteType (S : Scheme.{u}) :
    JacobsonSpace S ↔
      ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f],
        Set.MapsTo f (closedPoints T) (closedPoints S) := sorry

namespace JacobsonSpace

/-- A scheme is Jacobson if and only if every locally finite type morphism to it maps each closed
point to a closed point and induces a finite extension of residue fields there. -/
theorem iff_mapsTo_closedPoints_and_finite_residueField (S : Scheme.{u}) :
    JacobsonSpace S ↔
      ∀ {T : Scheme.{u}} (f : T ⟶ S) [LocallyOfFiniteType f], ∀ t : T,
        t ∈ closedPoints T →
          f t ∈ closedPoints S ∧
            Module.Finite (S.residueField (f t)) (T.residueField t) := sorry

end JacobsonSpace

end AlgebraicGeometry.Scheme
