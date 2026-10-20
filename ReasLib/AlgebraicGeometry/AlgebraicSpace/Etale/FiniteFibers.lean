module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Finite fibres of étale morphisms over a point of an algebraic space

A morphism from a scheme to an algebraic space has finite fibre over a point when
the preimage of that point under the induced map of underlying spaces is a finite
set. This module records the existence of an étale scheme covering with finite
fibres over a given point, and the corresponding affine étale test.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre of `|U| → |X|` over `x` is finite. -/
def finiteFibreOver {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (x : Points X) : Prop :=
  (Points.mapOfOver φ ⁻¹' {x}).Finite

/-- `finiteFibreOver φ x` is finiteness of the preimage of `x` under
`Points.mapOfOver φ`. -/
theorem finiteFibreOver_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (x : Points X) :
    finiteFibreOver φ x ↔ (Points.mapOfOver φ ⁻¹' {x}).Finite :=
  Iff.rfl

/-- Finiteness of the fibre of `|U| → |X|` over `x` is equivalent to finiteness of
the fibre of `Points.map φ`. -/
theorem finiteFibreOver_iff_map {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (φ : ofOver U ⟶ X) (x : Points X) :
    finiteFibreOver φ x ↔ (Points.map φ ⁻¹' {x}).Finite :=
  sorry

/-- There is a family of étale morphisms from schemes covering `X` with finite
fibres over `x`. -/
def existsEtaleCoverFiniteFibre {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
    (∀ i, Etale (φ i)) ∧
      (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
        ∀ i, finiteFibreOver (φ i) x

namespace existsEtaleCoverFiniteFibre

/-- An étale family of schemes whose images cover the points of `X` and whose
fibres over `x` are finite witnesses `existsEtaleCoverFiniteFibre`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} {I : Type u}
    {U : I → Over S} (φ : (i : I) → ofOver (U i) ⟶ X) [∀ i, Etale (φ i)]
    (hcover : ∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i)))
    (hfin : ∀ i, finiteFibreOver (φ i) x) :
    existsEtaleCoverFiniteFibre X x :=
  ⟨I, U, φ, fun i ↦ inferInstanceAs (Etale (φ i)), hcover, hfin⟩

/-- `existsEtaleCoverFiniteFibre X x` supplies an étale family of schemes covering
the points of `X` with finite fibres over `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : existsEtaleCoverFiniteFibre X x) :
    ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
      (∀ i, Etale (φ i)) ∧
        (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
          ∀ i, finiteFibreOver (φ i) x :=
  h

end existsEtaleCoverFiniteFibre

/-- The covering clause of `existsEtaleCoverFiniteFibre` is equivalent to
surjectivity of the induced coproduct morphism `∐ φ i`. -/
theorem existsEtaleCoverFiniteFibre_iff_coproductDesc {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) :
    existsEtaleCoverFiniteFibre X x ↔
      ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
        (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
          ∀ i, finiteFibreOver (φ i) x :=
  sorry

/-- Every étale morphism from an affine scheme to `X` has finite fibre over `x`. -/
def forallAffineEtaleFiniteFibre {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : Prop :=
  ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
    finiteFibreOver φ x

/-- `forallAffineEtaleFiniteFibre X x` means every étale morphism from an affine
scheme to `X` has finite fibre over `x`. -/
theorem forallAffineEtaleFiniteFibre_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) :
    forallAffineEtaleFiniteFibre X x ↔
      ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
        finiteFibreOver φ x :=
  Iff.rfl

namespace forallAffineEtaleFiniteFibre

/-- A universal finite-fibre condition on affine étale morphisms to `X`
witnesses `forallAffineEtaleFiniteFibre`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ (U : Over S) [IsAffine U.left] (φ : ofOver U ⟶ X) [Etale φ],
      finiteFibreOver φ x) :
    forallAffineEtaleFiniteFibre X x :=
  h

/-- Under `forallAffineEtaleFiniteFibre X x`, every étale morphism from an affine
scheme to `X` has finite fibre over `x`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : forallAffineEtaleFiniteFibre X x) (U : Over S) [IsAffine U.left]
    (φ : ofOver U ⟶ X) [Etale φ] : finiteFibreOver φ x :=
  h U φ

end forallAffineEtaleFiniteFibre

/-- An étale scheme covering with finite fibres over a point exists if and only
if every étale morphism from an affine scheme has finite fibre over that point. -/
theorem existsEtaleCoverFiniteFibre_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) :
    existsEtaleCoverFiniteFibre X x ↔ forallAffineEtaleFiniteFibre X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
