module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GenericallyFinite
import StacksCheckRecall

/-!
# Generically finite morphisms of algebraic spaces

For a quasi-separated finite-type morphism of algebraic spaces, finiteness of a
field-valued fibre over a codimension-zero point is equivalent to pointwise
quasi-finiteness over that point and to finiteness of the morphism after
shrinking the target to an open subspace. If the target is decent, these are
also equivalent to finiteness of the set-theoretic fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.21.1: Finiteness of a field-valued fibre over a codimension-zero
point, pointwise quasi-finiteness over that point, and finiteness over an open
target neighbourhood are equivalent. -/
@[stacks 0ACZ] #check (AlgebraicGeometry.AlgebraicSpace.tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0),
    List.TFAE
      [ Finite (Points (fieldFiber f p))
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x
      , ∃ Y' : OpenSubspace Y,
          Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι) ])

/- Lemma 68.21.1: If the target is decent, these conditions are also
equivalent to finiteness of the set-theoretic fibre. -/
@[stacks 0ACZ] #check (AlgebraicGeometry.AlgebraicSpace.tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open_of_isDecent :
    ∀
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f]
    [FiniteType f] [IsDecent Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0),
    List.TFAE
      [ Finite (Points (fieldFiber f p))
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x
      , ∃ Y' : OpenSubspace Y,
          Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι)
      , (fiberOver f (Points.mk p)).Finite ])

#check (AlgebraicGeometry.AlgebraicSpace.finite_fieldFiber_iff_quasiFiniteAt :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0),
    Finite (Points (fieldFiber f p)) ↔
      ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_iff_exists_isFinite_open :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0),
    (∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x) ↔
      ∃ Y' : OpenSubspace Y,
        Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι))

#check (AlgebraicGeometry.AlgebraicSpace.finite_fieldFiber_iff_exists_isFinite_open :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0),
    Finite (Points (fieldFiber f p)) ↔
      ∃ Y' : OpenSubspace Y,
        Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι))

#check (AlgebraicGeometry.AlgebraicSpace.finite_fiberOver_iff_finite_fieldFiber_of_isDecent :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0),
    (fiberOver f (Points.mk p)).Finite ↔ Finite (Points (fieldFiber f p)))
