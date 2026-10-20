module

public import Mathlib.CategoryTheory.Subobject.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support

/-! # Supports of algebraic-space subobjects

The image on points of a monomorphism depends only on its subobject class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace SubobjectPoints

/-- Isomorphic monomorphisms over an algebraic space have the same image on points. -/
private theorem range_eq_of_iso {S : Scheme.{u}} {X A B : AlgebraicSpace S}
    (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] (i : A ≅ B)
    (h : i.hom ≫ g = f) : Set.range (Points.map f) = Set.range (Points.map g) :=
  sorry

end SubobjectPoints

/-- The subobject represented by the inclusion of a closed subspace. -/
def ClosedSubspace.toSubobject {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) : Subobject X :=
  @Subobject.mk _ _ _ _ Z.ι Z.spec.2

/-- The support of a subobject is the image of any representing monomorphism on points. -/
@[no_expose] def subobjectPointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (P : Subobject X) : Set (Points X) :=
  Subobject.lift (fun {_} f _ => Set.range (Points.map f))
    (fun {_ _} f g _ _ i h => SubobjectPoints.range_eq_of_iso f g i h) P

/-- The support of the subobject of a closed subspace is its underlying point-set. -/
theorem ClosedSubspace.subobjectPointsSet_toSubobject {S : Scheme.{u}}
    {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    subobjectPointsSet Z.toSubobject = Z.pointsSet := by
  unfold subobjectPointsSet ClosedSubspace.toSubobject
  exact @Subobject.lift_mk _ _ _ _ _ _ _ Z.ι Z.spec.2

end AlgebraicGeometry.AlgebraicSpace
