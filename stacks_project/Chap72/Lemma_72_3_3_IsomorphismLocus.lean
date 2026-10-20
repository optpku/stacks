module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IsomorphismLocus

/-! # Isomorphism loci of morphisms of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.isomorphismLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Set (Points Y))

#check (AlgebraicGeometry.AlgebraicSpace.mem_isomorphismLocus_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {y : Points Y},
    y ∈ isomorphismLocus f ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ IsIso (restrictTo f U))

#check (AlgebraicGeometry.AlgebraicSpace.mem_isomorphismLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : OpenSubspace Y} (h : IsIso (restrictTo f U)),
    U.pointsSet ⊆ isomorphismLocus f)

#check (AlgebraicGeometry.AlgebraicSpace.isOpen_isomorphismLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    IsOpen (isomorphismLocus f))

end AlgebraicGeometry.AlgebraicSpace
