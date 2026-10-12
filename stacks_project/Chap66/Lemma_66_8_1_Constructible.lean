/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Topology.Constructible
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison

/-!
# Étale-local constructibility for algebraic spaces

A subset of the points of an algebraic space is checked for constructibility after inverse
image along étale morphisms from schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of a subset of `|X|` along a morphism from a scheme `U` over `S`, as a
subset of the underlying topological space of `U`. -/
def schemePreimage {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S} (f : ofOver U ⟶ X)
    (E : Set (Points X)) : Set U.left :=
  ofOver.pointsEquiv U ⁻¹' (Points.map f ⁻¹' E)

/-- A point of `U` lies in `schemePreimage f E` if and only if its image in `|X|` lies in `E`. -/
theorem mem_schemePreimage {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (f : ofOver U ⟶ X) (E : Set (Points X)) (u : U.left) :
    u ∈ schemePreimage f E ↔ Points.map f (ofOver.pointsEquiv U u) ∈ E :=
  Iff.rfl

/-- Inverse images of subsets of `|X|` are natural in morphisms of schemes over `S`. -/
theorem schemePreimage_comp {S : Scheme.{u}} {U V : Over S} {X : AlgebraicSpace S}
    (g : U ⟶ V) (f : ofOver V ⟶ X) (E : Set (Points X)) :
    schemePreimage (ofOverMap g ≫ f) E = g.left ⁻¹' schemePreimage f E :=
  sorry

/-- A subset of `|X|` is étale locally constructible if its inverse image in every scheme étale
over `X` is locally constructible. -/
def IsEtaleLocallyConstructible {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)) :
    Prop :=
  ∀ (U : Over S) (f : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf f → IsLocallyConstructible (schemePreimage f E)

/-- `IsEtaleLocallyConstructible E` is the universal étale-scheme locally constructible
condition. -/
theorem IsEtaleLocallyConstructible_def {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : Set (Points X)) :
    IsEtaleLocallyConstructible E ↔
      ∀ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f →
          IsLocallyConstructible (schemePreimage f E) :=
  Iff.rfl

namespace IsEtaleLocallyConstructible

/-- The universal étale-scheme locally constructible condition witnesses
`IsEtaleLocallyConstructible E`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)}
    (h : ∀ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf f →
        IsLocallyConstructible (schemePreimage f E)) :
    IsEtaleLocallyConstructible E :=
  h

/-- An étale locally constructible subset has locally constructible inverse image along every
étale morphism from a scheme. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)}
    (h : IsEtaleLocallyConstructible E) :
    ∀ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf f →
        IsLocallyConstructible (schemePreimage f E) :=
  h

/-- Inverse image along a given étale morphism from a scheme is locally constructible. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)}
    (h : IsEtaleLocallyConstructible E) {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@Etale)).presheaf f) :
    IsLocallyConstructible (schemePreimage f E) :=
  h U f hf

/-- Inverse images of `E` along étale morphisms from affine schemes are constructible. -/
def forallAffine {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)) : Prop :=
  ∀ (U : Over S) (f : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf f →
      IsAffine U.left → IsConstructible (schemePreimage f E)

/-- `forallAffine E` is the affine étale-scheme constructible condition. -/
theorem forallAffine_def {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)) :
    forallAffine E ↔
      ∀ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f →
          IsAffine U.left → IsConstructible (schemePreimage f E) :=
  Iff.rfl

namespace forallAffine

/-- The affine étale-scheme constructible condition witnesses `forallAffine E`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)}
    (h : ∀ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf f →
        IsAffine U.left → IsConstructible (schemePreimage f E)) :
    forallAffine E :=
  h

/-- An algebraic space satisfying `forallAffine E` has constructible inverse images of `E`
along étale morphisms from affine schemes. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)}
    (h : forallAffine E) :
    ∀ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf f →
        IsAffine U.left → IsConstructible (schemePreimage f E) :=
  h

/-- Inverse image along a given étale morphism from an affine scheme is constructible. -/
theorem apply {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)}
    (h : forallAffine E) {U : Over S} (f : ofOver U ⟶ X)
    (hf : (MorphismProperty.over (@Etale)).presheaf f) (hAff : IsAffine U.left) :
    IsConstructible (schemePreimage f E) :=
  h U f hf hAff

end forallAffine

/-- There is a surjective étale morphism from a scheme along which the inverse image of `E` is
locally constructible. -/
def existsSurjective {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)) : Prop :=
  ∃ (U : Over S) (f : ofOver U ⟶ X),
    (MorphismProperty.over (@Etale)).presheaf f ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
        IsLocallyConstructible (schemePreimage f E)

/-- `existsSurjective E` is the existence of a surjective étale scheme atlas with locally
constructible inverse image of `E`. -/
theorem existsSurjective_def {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)) :
    existsSurjective E ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
            IsLocallyConstructible (schemePreimage f E) :=
  Iff.rfl

namespace existsSurjective

/-- A surjective étale scheme atlas with locally constructible inverse image of `E` witnesses
`existsSurjective E`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)} {U : Over S}
    (f : ofOver U ⟶ X) (h_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f)
    (hE : IsLocallyConstructible (schemePreimage f E)) : existsSurjective E :=
  ⟨U, f, h_etale, h_surj, hE⟩

/-- An algebraic space satisfying `existsSurjective E` admits a surjective étale scheme atlas
with locally constructible inverse image of `E`. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {E : Set (Points X)}
    (h : existsSurjective E) :
    ∃ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf f ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
          IsLocallyConstructible (schemePreimage f E) :=
  h

end existsSurjective

/-- Étale local constructibility is equivalent to the affine étale constructible condition. -/
theorem iff_forallAffine {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)) :
    IsEtaleLocallyConstructible E ↔ forallAffine E :=
  sorry

/-- Étale local constructibility is equivalent to the existence of one surjective étale scheme
atlas with locally constructible inverse image. -/
theorem iff_existsSurjective {S : Scheme.{u}} {X : AlgebraicSpace S} (E : Set (Points X)) :
    IsEtaleLocallyConstructible E ↔ existsSurjective E :=
  sorry

/-- On a representable algebraic space, étale local constructibility reduces to ordinary local
constructibility of the corresponding subset of the scheme. -/
theorem ofOver_iff {S : Scheme.{u}} {T : Over S} (E : Set (Points (ofOver T))) :
    IsEtaleLocallyConstructible E ↔ IsLocallyConstructible (ofOver.pointsEquiv T ⁻¹' E) :=
  sorry

end IsEtaleLocallyConstructible

end AlgebraicGeometry.AlgebraicSpace
