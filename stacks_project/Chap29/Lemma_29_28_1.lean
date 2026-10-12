/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType

@[expose] public section

open AlgebraicGeometry

universe u v

#check (AlgebraicGeometry.Scheme.Hom.fiberStalkAt :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X), CommRingCat)

#check (AlgebraicGeometry.Scheme.Hom.residueFieldTrdegAt :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X), ℕ)

#check (AlgebraicGeometry.Scheme.Hom.stalkAlgebra :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
    Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x))

#check (relativeDimensionAtWith :
  ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S]
    (algebra : Algebra R S) (q : PrimeSpectrum S), WithBot ℕ∞)

#check (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X), WithBot ℕ∞)

#check (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_eq_topologicalKrullDimAt_asFiber :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
    f.fiberDimensionAt x = topologicalKrullDimAt (f.asFiber x))

#check (AlgebraicGeometry.Scheme.Hom.FiberDimension.at_eq_stalk_add_trdeg :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X),
    f.fiberDimensionAt x =
      ringKrullDim (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x) +
        AlgebraicGeometry.Scheme.Hom.residueFieldTrdegAt f x)

/- Lemma 29.28.1: for a locally finite type morphism, the local dimension of the fibre at its
distinguished point is the Krull dimension of the fibre stalk plus the transcendence degree of the
source residue field over the base residue field. -/
@[stacks 02FX] #check
  (AlgebraicGeometry.Scheme.Hom.FiberDimension.topologicalAt_eq_stalk_add_trdeg :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X),
      topologicalKrullDimAt (f.asFiber x) =
        ringKrullDim (AlgebraicGeometry.Scheme.Hom.fiberStalkAt f x) +
          AlgebraicGeometry.Scheme.Hom.residueFieldTrdegAt f x)
