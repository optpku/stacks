/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Faithfully flat standard-smooth presentations of relative dimension 0

`S(A)` is encoded as bundled presentations
`A → A[x₁,…,xₙ] ⧸ (f₁,…,fₙ)` whose Jacobian is a unit and whose quotient is
faithfully flat over `A`. Coefficient pushforward along `φ : A →+* A'` sends a
presentation to the corresponding presentation over `A'`.
-/

@[expose] public section

universe u

open MvPolynomial

namespace Algebra.IndEtaleEnvelope

/-- The naive pre-submersive presentation of a quotient
`A[x₁,…,xₙ] ⧸ (f₁,…,fₙ)` with matching variables and relations. -/
noncomputable def naivePresentation {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) :
    PreSubmersivePresentation A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range relations)) (Fin n) (Fin n) :=
  PreSubmersivePresentation.naive (fun i : Fin n ↦ i) Function.injective_id

/-- Jacobian of a standard-smooth presentation `A[x₁,…,xₙ] ⧸ (f₁,…,fₙ)`, as an
element of the quotient ring. -/
noncomputable def jacobianOfRelations {A : Type u} [CommRing A] (n : ℕ)
    (relations : Fin n → MvPolynomial (Fin n) A) :
    MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range relations) :=
  (naivePresentation n relations).jacobian

/-- A faithfully flat standard-smooth `A`-algebra of relative dimension 0,
presented as `A[x₁,…,xₙ] ⧸ (f₁,…,fₙ)` with invertible Jacobian. This is the
bundled data of an element of `S(A)`. -/
structure Presentation (A : Type u) [CommRing A] where
  /-- Number of variables, equal to the number of relations. -/
  n : ℕ
  /-- The relations `f₁,…,fₙ` in `A[x₁,…,xₙ]`. -/
  relations : Fin n → MvPolynomial (Fin n) A
  /-- The Jacobian determinant is a unit in the quotient. -/
  jacobian_isUnit : IsUnit (jacobianOfRelations n relations)
  /-- The presented algebra is faithfully flat over `A`. -/
  faithfullyFlat :
    Module.FaithfullyFlat A
      (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range relations))

namespace Presentation

variable {A : Type u} [CommRing A]

/-- The relation ideal `(f₁,…,fₙ)` of a presentation. -/
noncomputable def relationIdeal (P : Presentation A) : Ideal (MvPolynomial (Fin P.n) A) :=
  Ideal.span (Set.range P.relations)

/-- The presented algebra `A[x₁,…,xₙ] ⧸ (f₁,…,fₙ)` attached to an element of
`S(A)`. -/
abbrev Ring (P : Presentation A) : Type u :=
  MvPolynomial (Fin P.n) A ⧸ P.relationIdeal

/-- Jacobian of a presentation, as an element of `P.Ring`. -/
noncomputable def jacobian (P : Presentation A) : P.Ring :=
  jacobianOfRelations P.n P.relations

/-- Pack `n` relations together with the Jacobian-unit and faithfully-flat
conditions into an element of `S(A)`. -/
def ofRelations (n : ℕ) (relations : Fin n → MvPolynomial (Fin n) A)
    (jacobian_isUnit : IsUnit (jacobianOfRelations n relations))
    (faithfullyFlat :
      Module.FaithfullyFlat A
        (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range relations))) :
    Presentation A where
  n := n
  relations := relations
  jacobian_isUnit := jacobian_isUnit
  faithfullyFlat := faithfullyFlat

/-- Convert a bundled `S(A)` presentation into a mathlib submersive
presentation with matching variables and relations. -/
noncomputable def toSubmersive (P : Presentation A) :
    SubmersivePresentation A P.Ring (Fin P.n) (Fin P.n) where
  toPreSubmersivePresentation := naivePresentation P.n P.relations
  jacobian_isUnit := P.jacobian_isUnit

/-- A presentation in `S(A)` has invertible Jacobian and is faithfully flat. -/
theorem spec (P : Presentation A) :
    IsUnit (jacobian P) ∧ Module.FaithfullyFlat A P.Ring :=
  sorry

/-- A family of `n` relations in `n` variables lies in `S(A)` if and only if
the Jacobian is a unit and the quotient is faithfully flat. -/
theorem iff (n : ℕ) (relations : Fin n → MvPolynomial (Fin n) A) :
    (∃ (P : Presentation A) (h : P.n = n), h ▸ P.relations = relations) ↔
      IsUnit (jacobianOfRelations n relations) ∧
        Module.FaithfullyFlat A
          (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range relations)) :=
  sorry

/-- Coefficient pushforward of a presentation along `φ : A →+* A'`, sending
each relation `f` to the polynomial `f^φ` obtained by applying `φ` to
coefficients. -/
noncomputable def map {A' : Type u} [CommRing A'] (φ : A →+* A')
    (P : Presentation A) : Presentation A' where
  n := P.n
  relations := MvPolynomial.map φ ∘ P.relations
  jacobian_isUnit := sorry
  faithfullyFlat := sorry

/-- The relation ideal of a presentation is sent into the relation ideal of
its coefficient pushforward. -/
theorem map_span_le {A' : Type u} [CommRing A'] (φ : A →+* A')
    (P : Presentation A) :
    P.relationIdeal ≤ (P.map φ).relationIdeal.comap (MvPolynomial.map φ) :=
  sorry

/-- The vertical arrow of the inner presentation square, as the quotient map
induced by `MvPolynomial.map φ`. -/
noncomputable def mapRingHom {A' : Type u} [CommRing A'] (φ : A →+* A')
    (P : Presentation A) : P.Ring →+* (P.map φ).Ring :=
  Ideal.quotientMap (P.map φ).relationIdeal (MvPolynomial.map φ) (P.map_span_le φ)

/-- Inner presentation square: coefficient pushforward commutes with the
structure maps `A → P.Ring` and `A' → (P.map φ).Ring`. -/
theorem map_comp_algebraMap {A' : Type u} [CommRing A'] (φ : A →+* A')
    (P : Presentation A) :
    (P.mapRingHom φ).comp (algebraMap A P.Ring) =
      (algebraMap A' (P.map φ).Ring).comp φ :=
  sorry

end Presentation

end Algebra.IndEtaleEnvelope
