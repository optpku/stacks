module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import Mathlib.Topology.Maps.Basic

/-!
# Flat quasi-compact surjective morphisms are universally submersive
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat, quasi-compact, surjective morphism of algebraic spaces is universally
submersive. -/
instance UniversallySubmersive.of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f] :
    UniversallySubmersive f :=
  sorry

/-- A flat, quasi-compact, surjective morphism of algebraic spaces induces a
quotient map on canonical point spaces. -/
theorem isQuotientMapOnPoints_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY) :
    isQuotientMapOnPoints τX τY f :=
  Submersive.spec hX hY

/-- A subset of the target point space of a flat, quasi-compact, surjective
morphism of algebraic spaces is open if and only if its inverse image is open. -/
theorem isOpen_iff_preimage_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    (T : Set (Points Y)) :
    @IsOpen (Points Y) τY T ↔ @IsOpen (Points X) τX (Points.map f ⁻¹' T) :=
  ((isQuotientMapOnPoints_of_flat f hX hY).isCoinducing.isOpen_preimage (s := T)).symm

/-- A subset of the target point space of a flat, quasi-compact, surjective
morphism of algebraic spaces is closed if and only if its inverse image is
closed. -/
theorem isClosed_iff_preimage_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    (T : Set (Points Y)) :
    @IsClosed (Points Y) τY T ↔ @IsClosed (Points X) τX (Points.map f ⁻¹' T) :=
  ((isQuotientMapOnPoints_of_flat f hX hY).isCoinducing.isClosed_preimage (s := T)).symm

end AlgebraicGeometry.AlgebraicSpace
