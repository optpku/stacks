module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Submersive

/-!
# Flat quasi-compact surjective morphisms are universally submersive

A flat, quasi-compact, surjective morphism of algebraic spaces is a quotient
map on underlying point spaces, hence submersive and in fact universally
submersive.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.30.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat, quasi-compact,
surjective morphism of algebraic spaces over `S`. A subset `T ⊆ Points Y` is
open (resp. closed) if and only if `Points.map f ⁻¹' T` is open (resp. closed)
in `Points X`. In other words `f` is submersive, and in fact universally
submersive. -/
@[stacks 0413] #check (AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive.of_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicSpace.Flat f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.Surjective f],
    AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive f)

#check (AlgebraicGeometry.AlgebraicSpace.isQuotientMapOnPoints_of_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Flat f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY),
    isQuotientMapOnPoints τX τY f)

#check (AlgebraicGeometry.AlgebraicSpace.isOpen_iff_preimage_of_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Flat f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    (T : Set (Points Y)),
    @IsOpen (Points Y) τY T ↔ @IsOpen (Points X) τX (Points.map f ⁻¹' T))

#check (AlgebraicGeometry.AlgebraicSpace.isClosed_iff_preimage_of_flat :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Flat f]
    [AlgebraicGeometry.AlgebraicSpace.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicSpace.Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    (T : Set (Points Y)),
    @IsClosed (Points Y) τY T ↔ @IsClosed (Points X) τX (Points.map f ⁻¹' T))
