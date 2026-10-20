module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.QuasiFinite

/-!
# Conditions on a point in a fibre and quasi-finiteness

For a locally finite-type morphism of algebraic spaces, the four clauses compare
isolation, specialization, local topological and étale-local dimensions, and
quasi-finiteness at a point and an arbitrary compatible field-fibre lift.
The set-theoretic fibre carries its induced topology. Decency of the morphism,
the target, or both spaces supplies the indicated additional implications.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.18.9. Conditions (5), (6), (7), and (8) are equivalent. -/
@[stacks 0ACB] #check (AlgebraicGeometry.AlgebraicSpace.tfae_fieldFiber_isOpen_dimensionAt_quasiFiniteAt :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x),
    List.TFAE
      [ IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ])

/- For a decent morphism, condition (4) implies condition (5). -/
#check (AlgebraicGeometry.AlgebraicSpace.isOpen_fieldFiber_of_topologicalKrullDimAt_eq_zero :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Decent f]
    (p : FieldValuedPoint Y) (xtilde : Points (fieldFiber f p))
    (hdim : topologicalKrullDimAt xtilde = (0 : WithBot ℕ∞)),
    IsOpen ({xtilde} : Set (Points (fieldFiber f p))))

/- For a decent target, conditions (2), (3), (5), (6), (7), and (8) are equivalent. -/
#check (AlgebraicGeometry.AlgebraicSpace.tfae_fiberOver_isOpen_of_isDecent :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x),
    List.TFAE
      [ IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p)))
      , (IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
          (∀ x' : fiberOver f (Points.mk p),
            Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩))
      , IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ])

/- For decent source and target, all eight conditions are equivalent. -/
#check (AlgebraicGeometry.AlgebraicSpace.tfae_fiberOver_isOpen_of_isDecent_source_target :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y) (x : Points X)
    (xtilde : Points (fieldFiber f p)) (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x),
    List.TFAE
      [ topologicalKrullDimAt (⟨x, hx⟩ : fiberOver f (Points.mk p)) =
          (0 : WithBot ℕ∞)
      , IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p)))
      , (IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
          (∀ x' : fiberOver f (Points.mk p),
            Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩))
      , topologicalKrullDimAt xtilde = (0 : WithBot ℕ∞)
      , IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ])

