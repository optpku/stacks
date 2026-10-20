module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Étale coverings of reasonable algebraic spaces

An algebraic space is reasonable exactly when it admits a jointly surjective
family of étale scheme morphisms with individually universally bounded fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a family of étale morphisms from schemes covering `X` with
universally bounded fibres. -/
def existsEtaleCoverUniversallyBoundedFibres {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Prop :=
  ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
    (∀ i, Etale (φ i)) ∧
      (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
        ∀ i, universallyBoundedFibres (φ i)

namespace existsEtaleCoverUniversallyBoundedFibres

/-- An étale family of schemes whose images cover the points of `X` and whose
fibres are universally bounded gives an étale covering with universally bounded fibres. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type u}
    {U : I → Over S} (φ : (i : I) → ofOver (U i) ⟶ X) [∀ i, Etale (φ i)]
    (hcover : ∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i)))
    (hbound : ∀ i, universallyBoundedFibres (φ i)) :
    existsEtaleCoverUniversallyBoundedFibres X :=
  ⟨I, U, φ, (fun _ ↦ inferInstance), hcover, hbound⟩

/-- Existence of an étale covering with universally bounded fibres supplies a
family of schemes with the stated étaleness, point-covering, and fibre bounds. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsEtaleCoverUniversallyBoundedFibres X) :
    ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
      (∀ i, Etale (φ i)) ∧
        (∀ y : Points X, ∃ i, y ∈ Set.range (Points.mapOfOver (φ i))) ∧
          ∀ i, universallyBoundedFibres (φ i) :=
  h

end existsEtaleCoverUniversallyBoundedFibres

/-- Existence of a point-covering étale scheme family with universally bounded
fibres is equivalent to existence of such a family with surjective coproduct morphism. -/
theorem existsEtaleCoverUniversallyBoundedFibres_iff_coproductDesc
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    existsEtaleCoverUniversallyBoundedFibres X ↔
      ∃ (I : Type u) (U : I → Over S) (φ : (i : I) → ofOver (U i) ⟶ X),
        (∀ i, Etale (φ i)) ∧ Surjective (coproductDesc φ) ∧
          ∀ i, universallyBoundedFibres (φ i) :=
  sorry

/-- An algebraic space admits an étale scheme covering with universally bounded
fibres if and only if every affine étale scheme morphism into it has universally
bounded fibres. -/
theorem existsEtaleCoverUniversallyBoundedFibres_iff_isReasonable
    {S : Scheme.{u}} (X : AlgebraicSpace S) :
    existsEtaleCoverUniversallyBoundedFibres X ↔ IsReasonable X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
