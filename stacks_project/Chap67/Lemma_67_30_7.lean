module

public import stacks_project.Chap67.Definition_67_7_2_Submersive
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_30_5_Flat

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

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.30.7: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat, quasi-compact,
surjective morphism of algebraic spaces over `S`. A subset `T ⊆ Points Y` is
open (resp. closed) if and only if `Points.map f ⁻¹' T` is open (resp. closed)
in `Points X`. In other words `f` is submersive, and in fact universally
submersive. -/
@[stacks 0413]
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
  sorry

/-- A subset of the target point space of a flat, quasi-compact, surjective
morphism of algebraic spaces is open if and only if its inverse image is open. -/
theorem isOpen_iff_preimage_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    (T : Set (Points Y)) :
    @IsOpen (Points Y) τY T ↔ @IsOpen (Points X) τX (Points.map f ⁻¹' T) :=
  sorry

/-- A subset of the target point space of a flat, quasi-compact, surjective
morphism of algebraic spaces is closed if and only if its inverse image is
closed. -/
theorem isClosed_iff_preimage_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [QuasiCompact f] [Surjective f]
    {τX : TopologicalSpace (Points X)} {τY : TopologicalSpace (Points Y)}
    (hX : IsPointsTopology X τX) (hY : IsPointsTopology Y τY)
    (T : Set (Points Y)) :
    @IsClosed (Points Y) τY T ↔ @IsClosed (Points X) τX (Points.map f ⁻¹' T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
