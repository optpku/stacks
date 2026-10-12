/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Residue-identified Artinian factorizations of field-valued morphisms

A field-valued morphism `σ : Spec(k) ⟶ S` may factor as `Spec(k) ⟶ Spec(A) ⟶ S`
with `A` Artinian local and with `Spec(k) ⟶ Spec(A)` induced by a ring map
`A → k` identifying `k` with the residue field of `A`.
-/

@[expose] public section

open CategoryTheory IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The morphism `Spec(k) ⟶ Spec(A)` induced by a residue-field identification
`ResidueField A ≃+* k`. -/
def residueSpecMap {k A : Type u} [Field k] [CommRing A] [IsLocalRing A]
    (e : ResidueField A ≃+* k) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (e.toRingHom.comp (residue A)))

/-- A factorization `Spec(k) ⟶ Spec(A) ⟶ S` of a field-valued morphism, with `A`
Artinian local and with `Spec(k) ⟶ Spec(A)` induced by a residue-field
identification. -/
structure ArtinianResidueFactorization {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) (A : Type u)
    [CommRing A] [IsLocalRing A] [IsArtinianRing A] where
  /-- Identification of the residue field of `A` with `k`. -/
  residueFieldIso : ResidueField A ≃+* k
  /-- The morphism `Spec(A) ⟶ S`. -/
  toS : Spec (CommRingCat.of A) ⟶ S
  /-- The residue identification and `toS` recover `σ`. -/
  factor : residueSpecMap residueFieldIso ≫ toS = σ

namespace ArtinianResidueFactorization

/-- Bundle a residue identification and a morphism `Spec(A) ⟶ S` commuting with
`σ` into an Artinian residue factorization. -/
def of {S : Scheme.{u}} {k A : Type u} [Field k] [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] {σ : Spec (CommRingCat.of k) ⟶ S}
    (residueFieldIso : ResidueField A ≃+* k)
    (toS : Spec (CommRingCat.of A) ⟶ S)
    (factor : residueSpecMap residueFieldIso ≫ toS = σ) :
    ArtinianResidueFactorization σ A where
  residueFieldIso := residueFieldIso
  toS := toS
  factor := factor

/-- The identity factorization `Spec(k) ⟶ Spec(k) ⟶ S`. -/
def ofField {S : Scheme.{u}} {k : Type u} [Field k]
    (σ : Spec (CommRingCat.of k) ⟶ S) : ArtinianResidueFactorization σ k where
  residueFieldIso :=
    (Ideal.quotEquivOfEq maximalIdeal_eq_bot).trans (RingEquiv.quotientBot k)
  toS := σ
  factor := sorry

/-- The first arrow `Spec(k) ⟶ Spec(A)` of a residue factorization. -/
def residueSpec {S : Scheme.{u}} {k A : Type u} [Field k] [CommRing A]
    [IsLocalRing A] [IsArtinianRing A] {σ : Spec (CommRingCat.of k) ⟶ S}
    (F : ArtinianResidueFactorization σ A) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) :=
  residueSpecMap F.residueFieldIso

/-- The ring map `A → k` identifying `k` with the residue field of `A`. -/
def residueToHom {S : Scheme.{u}} {k A : Type u} [Field k] [CommRing A]
    [IsLocalRing A] [IsArtinianRing A] {σ : Spec (CommRingCat.of k) ⟶ S}
    (F : ArtinianResidueFactorization σ A) : A →+* k :=
  F.residueFieldIso.toRingHom.comp (residue A)

/-- An Artinian residue factorization commutes, and its residue identification is
bijective. -/
theorem spec {S : Scheme.{u}} {k A : Type u} [Field k] [CommRing A]
    [IsLocalRing A] [IsArtinianRing A] {σ : Spec (CommRingCat.of k) ⟶ S}
    (F : ArtinianResidueFactorization σ A) :
    residueSpecMap F.residueFieldIso ≫ F.toS = σ ∧
      Function.Bijective F.residueFieldIso := sorry

end ArtinianResidueFactorization

end AlgebraicGeometry
