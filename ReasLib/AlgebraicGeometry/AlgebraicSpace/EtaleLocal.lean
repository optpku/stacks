module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Étale-local properties of algebraic spaces

An étale-local property of schemes holds on one surjective étale scheme atlas of an
algebraic space if and only if it holds on every étale scheme mapping to that space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There exists a scheme `U` over `S` and a surjective étale morphism `U ⟶ X` such that
`U` has property `P`. -/
def existsSurjectiveEtale {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : AlgebraicSpace S) : Prop :=
  ∃ (U : Over S) (f : ofOver U ⟶ X),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧ P U.left

/-- `existsSurjectiveEtale P X` is the existence of a representable étale locally-surjective
atlas from a scheme with property `P`. -/
theorem existsSurjectiveEtale_def {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : AlgebraicSpace S) :
    existsSurjectiveEtale P X ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧ P U.left :=
  Iff.rfl

namespace existsSurjectiveEtale

/-- A representable étale locally-surjective atlas from a scheme with property `P` witnesses
`existsSurjectiveEtale P X`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (f : ofOver U ⟶ X)
    (h_etale : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f)
    (hP : P U.left) : existsSurjectiveEtale P X :=
  ⟨U, f, h_etale, h_surj, hP⟩

/-- An algebraic space satisfying `existsSurjectiveEtale P X` admits a representable étale
locally-surjective atlas from a scheme with property `P`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale P X) :
    ∃ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧ P U.left :=
  h

end existsSurjectiveEtale

/-- An algebraic space has an étale-local scheme property `P` if it admits a representable
étale locally-surjective atlas from a scheme with property `P`. -/
def hasEtaleLocal {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (X : AlgebraicSpace S) : Prop :=
  existsSurjectiveEtale P X

/-- `hasEtaleLocal P X` is the existence of a representable étale locally-surjective atlas from a
scheme with property `P`. -/
theorem hasEtaleLocal_def {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (X : AlgebraicSpace S) :
    hasEtaleLocal P X ↔ existsSurjectiveEtale P X :=
  Iff.rfl

/-- Every étale morphism from a scheme `U` over `S` to `X` has `P U.left`. -/
def forallEtale {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : AlgebraicSpace S) : Prop :=
  ∀ (U : Over S) (f : ofOver U ⟶ X),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f → P U.left

/-- `forallEtale P X` is the statement that every étale morphism from a scheme to `X` has
property `P` on the source. -/
theorem forallEtale_def {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    (X : AlgebraicSpace S) :
    forallEtale P X ↔
      ∀ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f → P U.left :=
  Iff.rfl

namespace forallEtale

/-- The universal étale-scheme condition witnesses `forallEtale P X`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f → P U.left) :
    forallEtale P X :=
  h

/-- If `forallEtale P X`, then every étale morphism from a scheme `U` to `X` has `P U.left`. -/
theorem apply {S : Scheme.{u}} {P : ObjectProperty Scheme.{u}} {X : AlgebraicSpace S}
    (h : forallEtale P X) {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf f) :
    P U.left :=
  h U f hf

end forallEtale

/-- An étale-local property of schemes holds on some surjective étale scheme atlas of an
algebraic space if and only if it holds on every étale scheme mapping to that space. -/
theorem existsSurjectiveEtale_iff_forallEtale {S : Scheme.{u}}
    (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]
    (X : AlgebraicSpace S) : existsSurjectiveEtale P X ↔ forallEtale P X := sorry

/-- A scheme over `S` admits a surjective étale atlas with an étale-local property `P`
if and only if its underlying scheme has property `P`. -/
theorem existsSurjectiveEtale_ofOver {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (T : Over S) :
    existsSurjectiveEtale P (ofOver T) ↔ P T.left := sorry

/-- If `T` is a scheme over `S`, then every étale morphism from a scheme to `ofOver T` has
property `P` if and only if `T.left` has property `P`. -/
theorem forallEtale_ofOver {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (T : Over S) :
    forallEtale P (ofOver T) ↔ P T.left := sorry

/-- An algebraic space isomorphic to the space represented by `T` admits a surjective
étale atlas with an étale-local property `P` if and only if `T.left` has property `P`. -/
theorem existsSurjectiveEtale_iso {S : Scheme.{u}} (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] {X : AlgebraicSpace S} {T : Over S}
    (e : X ≅ ofOver T) : existsSurjectiveEtale P X ↔ P T.left := sorry

end AlgebraicGeometry.AlgebraicSpace
