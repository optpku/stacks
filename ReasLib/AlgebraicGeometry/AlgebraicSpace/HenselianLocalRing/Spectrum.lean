/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Stalk.Henselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedPoints.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement


/-!
# Henselization of a decent algebraic space at a point

A Type-u henselization of the stalk at an affine elementary étale neighbourhood
realizes `Spec(𝒪_{X,x}^h)` as an algebraic space over `S`, together with the
open complement of a closed point and the punctured henselization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Henselization

/-- The structural morphism obtained from a henselization of a stalk of a represented
étale neighbourhood, followed by its map to the ambient algebraic space. -/
def fromNeighborhood {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Over S) (a : ofOver T ⟶ X) (p : T.left) (R : Type u)
    [CommRing R] [Algebra (T.left.presheaf.stalk p) R]
    [IsHenselizationOf (T.left.presheaf.stalk p) R] :
    ofOver (Over.mk (Scheme.Henselization.map T.left p R ≫ T.hom)) ⟶ X :=
  ofOverMap (Over.homMk (Scheme.Henselization.map T.left p R)) ≫ a

/-- The inclusion of the punctured spectrum, with its structure map to the base explicit. -/
def puncturedι {S : Scheme.{u}} (R : Type u) [CommRing R] [IsLocalRing R]
    (a : Spec (CommRingCat.of R) ⟶ S) :
    ofOver (Over.mk ((PuncturedSpectrum.puncturedOpen R).ι ≫ a)) ⟶
      ofOver (Over.mk a) :=
  ofOverMap (Over.homMk (PuncturedSpectrum.puncturedOpen R).ι)

/-- The punctured spectrum includes as an open immersion over any base. -/
theorem isOpenImmersion_puncturedι {S : Scheme.{u}} (R : Type u)
    [CommRing R] [IsLocalRing R] (a : Spec (CommRingCat.of R) ⟶ S) :
    IsOpenImmersion (puncturedι R a) := sorry

/-- A henselization of the stalk of an étale represented neighbourhood is flat over
the ambient algebraic space. -/
theorem flat_fromNeighborhood {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Over S) (a : ofOver T ⟶ X) [Etale a] (p : T.left) (R : Type u)
    [CommRing R] [Algebra (T.left.presheaf.stalk p) R]
    [IsHenselizationOf (T.left.presheaf.stalk p) R] :
    Flat (fromNeighborhood T a p R) := sorry

end Henselization

/-- The spectrum of the Type-u henselization of a neighbourhood stalk at `x`. -/
def henselizationScheme {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : Scheme.{u} :=
  let _ := hN
  Spec (CommRingCat.of R)

/-- `Spec(𝒪_{X,x}^h)` as a scheme over `S`, via the structure morphism of a supplied
affine elementary étale neighbourhood. -/
def henselizationOver {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : Over S :=
  let _ := hN
  Over.mk
    (Scheme.Henselization.map N.scheme
        N.point R ≫
      N.toOver.hom)

/-- `Spec(𝒪_{X,x}^h)` as an algebraic space over `S`. -/
def henselizationSpace {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : AlgebraicSpace S :=
  ofOver (henselizationOver X x N hN R)

/-- The canonical morphism `Spec(𝒪_{X,x}^h) ⟶ X` of algebraic spaces over `S`. -/
def fromHenselization {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : henselizationSpace X x N hN R ⟶ X :=
  Henselization.fromNeighborhood N.toOver N.hom N.point R

/-- The closed point of `Spec(𝒪_{X,x}^h)`, as a point of `henselizationSpace X x N hN R`. -/
def henselizationClosedPoint {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : Points (henselizationSpace X x N hN R) :=
  ofOver.pointsEquiv (henselizationOver X x N hN R)
    (IsLocalRing.closedPoint R)

/-- The canonical morphism `Spec(𝒪_{X,x}^h) ⟶ X` sends the closed point of the
henselization to `x`. -/
theorem fromHenselization_map_closedPoint {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :
    Points.map (fromHenselization X x N hN R) (henselizationClosedPoint X x N hN R) = x := sorry

/-- The punctured spectrum of the henselization, as a scheme over `S`. -/
def henselizationPuncturedOver {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : Over S :=
  Over.mk
    ((PuncturedSpectrum.puncturedOpen R).ι ≫
      (henselizationOver X x N hN R).hom)

/-- The punctured spectrum `Spec(𝒪_{X,x}^h) \ {𝔪_x^h}` as an algebraic space over
`S`. -/
def henselizationPunctured {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : AlgebraicSpace S :=
  ofOver (henselizationPuncturedOver X x N hN R)

/-- The open immersion of the punctured henselization into `Spec(𝒪_{X,x}^h)`. -/
def henselizationPuncturedι {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] : henselizationPunctured X x N hN R ⟶ henselizationSpace X x N hN R :=
  Henselization.puncturedι R (henselizationOver X x N hN R).hom

/-- The punctured spectrum of the henselization factors through the inverse image of
`X \ {x}` along `fromHenselization`. -/
theorem henselization_open_le {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R] :
    ∃ φ : henselizationPunctured X x N hN R ⟶
        openInverseImage (fromHenselization X x N hN R) (closedPointComplementι X hx),
      φ ≫ openInverseImageι (fromHenselization X x N hN R) (closedPointComplementι X hx) =
        henselizationPuncturedι X x N hN R := sorry

end AlgebraicGeometry.AlgebraicSpace
