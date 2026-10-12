/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Stalk.Henselization
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap68.Lemma_68_11_4
public import stacks_project.Chap68.Lemma_68_14_6

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

/-- A chosen affine elementary étale neighbourhood of a point of a decent algebraic
space, as in Lemma 68.11.4. -/
def affineElementaryNeighborhood {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : EtaleNeighborhood X x :=
  (EtaleNeighborhood.exists_affine_elementary X x).choose

/-- The chosen neighbourhood is affine, elementary, and has a unique point over `x`. -/
theorem affineElementaryNeighborhood_spec {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) :
    IsAffine (affineElementaryNeighborhood X x).scheme ∧
      Points.mapOfOver (affineElementaryNeighborhood X x).hom ⁻¹' {x} =
        {(affineElementaryNeighborhood X x).point} ∧
      (affineElementaryNeighborhood X x).IsElementary :=
  sorry

/-- The open complement `X \ {x}` of a closed point of a decent algebraic space. -/
def closedPointComplement {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) : AlgebraicSpace S :=
  @closedImmersionComplement _ _ _ (X.fromSpecResidueField x)
    (isClosedImmersion_fromSpecResidueField hx)

/-- The open immersion `X \ {x} ⟶ X` of a closed point of a decent algebraic space. -/
def closedPointComplementι {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) :
    closedPointComplement X hx ⟶ X :=
  @closedImmersionComplementι _ _ _ (X.fromSpecResidueField x)
    (isClosedImmersion_fromSpecResidueField hx)

/-- The complement of a closed point is an open immersion into `X`. -/
instance instIsOpenImmersion_closedPointComplementι {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) :
    IsOpenImmersion (closedPointComplementι X hx) :=
  @instIsOpenImmersion_closedImmersionComplementι _ _ _
    (X.fromSpecResidueField x) (isClosedImmersion_fromSpecResidueField hx)

/-- A Type-u henselization of the stalk of a chosen affine elementary étale
neighbourhood of `x`. -/
def henselizationRing {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Type u :=
  (IsHenselizationOf.exists_henselization
      ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
        (affineElementaryNeighborhood X x).point)).choose

/-- The chosen henselization ring is a commutative ring. -/
instance instCommRing_henselizationRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) : CommRing (henselizationRing X x) :=
  (IsHenselizationOf.exists_henselization
      ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
        (affineElementaryNeighborhood X x).point)).choose_spec.choose

/-- The chosen henselization ring is an algebra over the neighbourhood stalk. -/
instance instAlgebra_henselizationRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) :
    Algebra
      ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
        (affineElementaryNeighborhood X x).point)
      (henselizationRing X x) :=
  (IsHenselizationOf.exists_henselization
      ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
        (affineElementaryNeighborhood X x).point)).choose_spec.choose_spec.choose

/-- The chosen ring is a henselization of the neighbourhood stalk. -/
instance instIsHenselizationOf_henselizationRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    IsHenselizationOf
      ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
        (affineElementaryNeighborhood X x).point)
      (henselizationRing X x) :=
  (IsHenselizationOf.exists_henselization
      ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
        (affineElementaryNeighborhood X x).point)).choose_spec.choose_spec.choose_spec

/-- The chosen henselization ring, together with its algebra structure, is a
henselization of the neighbourhood stalk. -/
theorem henselizationRing_spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    ∃ (_ : CommRing (henselizationRing X x))
      (_ : Algebra
        ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
          (affineElementaryNeighborhood X x).point)
        (henselizationRing X x)),
      IsHenselizationOf
        ((affineElementaryNeighborhood X x).scheme.presheaf.stalk
          (affineElementaryNeighborhood X x).point)
        (henselizationRing X x) :=
  sorry

/-- The spectrum of the Type-u henselization of a neighbourhood stalk at `x`. -/
def henselizationScheme {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Scheme.{u} :=
  Spec (CommRingCat.of (henselizationRing X x))

/-- `Spec(𝒪_{X,x}^h)` as a scheme over `S`, via the structure morphism of a chosen
affine elementary étale neighbourhood. -/
def henselizationOver {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Over S :=
  Over.mk
    (Scheme.Henselization.map (affineElementaryNeighborhood X x).scheme
        (affineElementaryNeighborhood X x).point (henselizationRing X x) ≫
      (affineElementaryNeighborhood X x).toOver.hom)

/-- `Spec(𝒪_{X,x}^h)` as an algebraic space over `S`. -/
def henselizationSpace {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : AlgebraicSpace S :=
  ofOver (henselizationOver X x)

/-- The canonical morphism `Spec(𝒪_{X,x}^h) ⟶ X` of algebraic spaces over `S`. -/
def fromHenselization {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : henselizationSpace X x ⟶ X :=
  ofOverMap
      (Over.homMk
        (Scheme.Henselization.map (affineElementaryNeighborhood X x).scheme
          (affineElementaryNeighborhood X x).point (henselizationRing X x))) ≫
    (affineElementaryNeighborhood X x).hom

/-- The closed point of `Spec(𝒪_{X,x}^h)`, as a point of `henselizationSpace X x`. -/
def henselizationClosedPoint {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Points (henselizationSpace X x) :=
  ofOver.pointsEquiv (henselizationOver X x)
    (IsLocalRing.closedPoint (henselizationRing X x))

/-- The canonical morphism `Spec(𝒪_{X,x}^h) ⟶ X` sends the closed point of the
henselization to `x`. -/
theorem fromHenselization_map_closedPoint {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) :
    Points.map (fromHenselization X x) (henselizationClosedPoint X x) = x :=
  sorry

/-- The punctured spectrum of the henselization, as a scheme over `S`. -/
def henselizationPuncturedOver {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Over S :=
  Over.mk
    ((PuncturedSpectrum.puncturedOpen (henselizationRing X x)).ι ≫
      (henselizationOver X x).hom)

/-- The punctured spectrum `Spec(𝒪_{X,x}^h) \ {𝔪_x^h}` as an algebraic space over
`S`. -/
def henselizationPunctured {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : AlgebraicSpace S :=
  ofOver (henselizationPuncturedOver X x)

/-- The open immersion of the punctured henselization into `Spec(𝒪_{X,x}^h)`. -/
def henselizationPuncturedι {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : henselizationPunctured X x ⟶ henselizationSpace X x :=
  ofOverMap (Over.homMk (PuncturedSpectrum.puncturedOpen (henselizationRing X x)).ι)

/-- The punctured henselization includes as an open immersion. -/
instance instIsOpenImmersion_henselizationPuncturedι {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    IsOpenImmersion (henselizationPuncturedι X x) :=
  sorry

/-- The punctured spectrum of the henselization factors through the inverse image of
`X \ {x}` along `fromHenselization`. -/
theorem henselization_open_le {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) :
    ∃ φ : henselizationPunctured X x ⟶
        openInverseImage (fromHenselization X x) (closedPointComplementι X hx),
      φ ≫ openInverseImageι (fromHenselization X x) (closedPointComplementι X hx) =
        henselizationPuncturedι X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
