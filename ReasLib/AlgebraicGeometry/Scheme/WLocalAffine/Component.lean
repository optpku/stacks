/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Component localizations of a vanishing pattern

Given a commutative ring `A` and a finite subset `E`, vanishing patterns index
the complementary decompositions `E = E' ⨿ E''`. Each pattern determines the
locally closed stratum `Z(E', E'') = D(∏ E') ∩ V(span E'')` and the
localization `A_Z^~ = S⁻¹A`, where `S` is the preimage of the units of `(A / I)_f`.
-/

@[expose] public section

universe u

open Finset

namespace AlgebraicGeometry.Scheme.WLocalAffine

variable {A : Type u} [CommRing A]

/-- A vanishing pattern on a finite subset `E` records, for each element of `E`,
whether it is treated as nonvanishing. This indexes complementary decompositions
`E = E' ⨿ E''`. -/
abbrev VanishingPattern (E : Finset A) : Type u :=
  {x // x ∈ E} → Bool

/-- Vanishing patterns on a finite subset form a finite type of cardinality
`2 ^ E.card`. -/
instance instFiniteVanishingPattern (E : Finset A) : Finite (VanishingPattern E) :=
  inferInstance

/-- The vanishing pattern associated to a complementary decomposition
`E = E' ⨿ E''`, sending elements of `E'` to `true`. -/
noncomputable def ofComplementary (E E' E'' : Finset A)
    (hdisj : Disjoint (E' : Set A) (E'' : Set A))
    (hunion : (E' : Set A) ∪ (E'' : Set A) = (E : Set A)) :
    VanishingPattern E := fun x =>
  have := hdisj
  have := hunion
  @decide (x.1 ∈ E') (Classical.dec _)

/-- The nonvanishing part `E'` of a vanishing pattern. -/
def nonvanishing {E : Finset A} (p : VanishingPattern E) : Finset A :=
  (E.attach.filter fun x => p x = true).map (Function.Embedding.subtype _)

/-- The vanishing part `E''` of a vanishing pattern. -/
def vanishing {E : Finset A} (p : VanishingPattern E) : Finset A :=
  (E.attach.filter fun x => p x = false).map (Function.Embedding.subtype _)

/-- Reconstructing a complementary decomposition recovers the nonvanishing part. -/
theorem nonvanishing_ofComplementary (E E' E'' : Finset A)
    (hdisj : Disjoint (E' : Set A) (E'' : Set A))
    (hunion : (E' : Set A) ∪ (E'' : Set A) = (E : Set A)) :
    nonvanishing (ofComplementary E E' E'' hdisj hunion) = E' := sorry

/-- Reconstructing a complementary decomposition recovers the vanishing part. -/
theorem vanishing_ofComplementary (E E' E'' : Finset A)
    (hdisj : Disjoint (E' : Set A) (E'' : Set A))
    (hunion : (E' : Set A) ∪ (E'' : Set A) = (E : Set A)) :
    vanishing (ofComplementary E E' E'' hdisj hunion) = E'' := sorry

/-- The nonvanishing and vanishing parts of a pattern are complementary in `E`. -/
theorem nonvanishing_union_vanishing {E : Finset A} (p : VanishingPattern E) :
    (nonvanishing p : Set A) ∪ (vanishing p : Set A) = (E : Set A) := sorry

/-- The nonvanishing and vanishing parts of a pattern are disjoint. -/
theorem disjoint_nonvanishing_vanishing {E : Finset A} (p : VanishingPattern E) :
    Disjoint (nonvanishing p : Set A) (vanishing p : Set A) := sorry

/-- The basic-open generator `f = ∏ E'` of the stratum associated to a vanishing
pattern. -/
def stratumF {E : Finset A} (p : VanishingPattern E) : A :=
  (nonvanishing p).prod id

/-- The vanishing ideal `I = span E''` of the stratum associated to a vanishing
pattern. -/
def stratumIdeal {E : Finset A} (p : VanishingPattern E) : Ideal A :=
  Ideal.span (vanishing p : Set A)

/-- Global sections of the locally closed stratum, as the away-localization
`(A / I)_f`. -/
noncomputable abbrev stratumSections {E : Finset A} (p : VanishingPattern E) : Type u :=
  Localization.Away (Ideal.Quotient.mk (stratumIdeal p) (stratumF p))

/-- The canonical `A`-algebra structure on `(A / I)_f` via `A → A / I → (A / I)_f`. -/
noncomputable instance instAlgebraStratumSections {E : Finset A}
    (p : VanishingPattern E) : Algebra A (stratumSections p) :=
  ((algebraMap (A ⧸ stratumIdeal p) (stratumSections p)).comp
    (Ideal.Quotient.mk (stratumIdeal p))).toAlgebra

/-- The multiplicative set `S ⊆ A` of elements mapping to units of `(A / I)_f`. -/
noncomputable def unitsPreimage {E : Finset A} (p : VanishingPattern E) : Submonoid A :=
  (IsUnit.submonoid (stratumSections p)).comap (algebraMap A (stratumSections p))

/-- Membership in `unitsPreimage p` is invertibility in `(A / I)_f`. -/
theorem mem_unitsPreimage_iff {E : Finset A} (p : VanishingPattern E) (a : A) :
    a ∈ unitsPreimage p ↔ IsUnit (algebraMap A (stratumSections p) a) := sorry

/-- The component localization `A_{Z(E', E'')}^~ = S⁻¹A` at the elements
mapping to units in the stratum sections. -/
noncomputable abbrev componentAlgebra {E : Finset A} (p : VanishingPattern E) : Type u :=
  Localization (unitsPreimage p)

/-- The component algebra is the localization of `A` at `unitsPreimage p`. -/
noncomputable instance instIsLocalizationComponentAlgebra {E : Finset A}
    (p : VanishingPattern E) :
    IsLocalization (unitsPreimage p) (componentAlgebra p) := inferInstance

end AlgebraicGeometry.Scheme.WLocalAffine
