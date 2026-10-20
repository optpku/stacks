/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Valuative squares for morphisms of algebraic stacks

A valuative commutative square over a morphism `f : X ⟶ Y` of algebraic stacks
is the solid 2-commutative diagram `Spec(K) ⟶ X`, `Spec(R) ⟶ Y` with vertical
arrow `Spec(K) ⟶ Spec(R)`, where `R` is a valuation ring and `K` is a field of
fractions of `R`. The 2-cell is an isomorphism `j ≫ y ≅ x ≫ f`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A solid valuative square of algebraic stacks consists of a valuation domain,
its fraction field, two stack arrows over the base, and an invertible comparison
from the vertical composite to the top arrow followed by the given morphism. -/
abbrev ValuativeCommSq {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :=
  Σ b : AlgebraicGeometry.ValuativeCommSq (𝟙 S),
    Σ i₁ : GroupoidsOver.slice
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap b.R b.K)) ≫ b.i₂)) ⟶ X,
      Σ i₂ : GroupoidsOver.slice (Over.mk b.i₂) ⟶ Y,
        overMap (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap b.R b.K))) rfl) ≫
          i₂ ≅ i₁ ≫ f

namespace ValuativeCommSq

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}

/-- The underlying scheme-valued square over the identity of the base. -/
abbrev baseSquare (sq : ValuativeCommSq f) :
    AlgebraicGeometry.ValuativeCommSq (𝟙 S) := sq.1

/-- The valuation domain of a valuative square. -/
abbrev R (sq : ValuativeCommSq f) : Type u := sq.baseSquare.R

/-- The commutative ring structure of the valuation domain. -/
abbrev commRing (sq : ValuativeCommSq f) : CommRing sq.R := sq.baseSquare.commRing

/-- The valuation ring is an integral domain. -/
abbrev domain (sq : ValuativeCommSq f) : IsDomain sq.R := sq.baseSquare.domain

/-- The valuation-ring structure of the domain. -/
abbrev valuationRing (sq : ValuativeCommSq f) : ValuationRing sq.R :=
  sq.baseSquare.valuationRing

/-- The fraction field of a valuative square. -/
abbrev K (sq : ValuativeCommSq f) : Type u := sq.baseSquare.K

/-- The field structure of the fraction field. -/
abbrev field (sq : ValuativeCommSq f) : Field sq.K := sq.baseSquare.field

/-- The algebra structure from the valuation domain to its fraction field. -/
abbrev algebra (sq : ValuativeCommSq f) : Algebra sq.R sq.K := sq.baseSquare.algebra

/-- The field is a fraction ring of the valuation domain. -/
abbrev isFractionRing (sq : ValuativeCommSq f) : IsFractionRing sq.R sq.K :=
  sq.baseSquare.isFractionRing

/-- The structure morphism of the valuation-ring spectrum over the base. -/
abbrev structureHom (sq : ValuativeCommSq f) : Spec (.of sq.R) ⟶ S :=
  sq.baseSquare.i₂

/-- The top stack arrow from the fraction-field spectrum. -/
abbrev i₁ (sq : ValuativeCommSq f) :
    GroupoidsOver.slice
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)) ⟶
      X := sq.2.1

/-- The bottom stack arrow from the valuation-ring spectrum. -/
abbrev i₂ (sq : ValuativeCommSq f) :
    GroupoidsOver.slice (Over.mk sq.structureHom) ⟶ Y := sq.2.2.1

/-- The invertible comparison from the vertical composite to the top composite. -/
abbrev iso (sq : ValuativeCommSq f) :
    overMap (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl) ≫
      sq.i₂ ≅ sq.i₁ ≫ f := sq.2.2.2

/-- Construct a valuative commutative square from a valuation ring, a field of
fractions, a structure morphism over `S`, the two solid arrows, and a 2-cell. -/
def of (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (structureHom : Spec (.of R) ⟶ S)
    (i₁ :
      GroupoidsOver.slice
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶
        X)
    (i₂ : GroupoidsOver.slice (Over.mk structureHom) ⟶ Y)
    (iso :
      overMap (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) ≫ i₂ ≅
        i₁ ≫ f) :
    ValuativeCommSq f :=
  ⟨{ R := R
     K := K
     i₁ := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom
     i₂ := structureHom
     commSq := ⟨Category.comp_id _⟩ }, i₁, i₂, iso⟩

/-- `Spec(R)` as a scheme over `S`. -/
abbrev specR (sq : ValuativeCommSq f) : Over S := Over.mk sq.structureHom

/-- `Spec(K)` as a scheme over `S`, via the algebra map `R → K`. -/
abbrev specK (sq : ValuativeCommSq f) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.structureHom)

/-- The vertical morphism `Spec(K) ⟶ Spec(R)` of algebraic stacks over `S`. -/
abbrev verticalMap (sq : ValuativeCommSq f) :
    GroupoidsOver.slice sq.specK ⟶ GroupoidsOver.slice sq.specR :=
  overMap (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl)

/-- The vertical arrow is `overMap` of `Over.homMk` of `Spec.map` of the algebra map. -/
theorem verticalMap_eq (sq : ValuativeCommSq f) :
    sq.verticalMap =
      overMap (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl) :=
  sorry

/-- The 2-cell `j ≫ y ≅ x ≫ f` of a solid valuative square. -/
def two_commute (sq : ValuativeCommSq f) :
    sq.verticalMap ≫ sq.i₂ ≅ sq.i₁ ≫ f :=
  sq.iso

/-- The solid valuative square, viewed as a 2-commutative cospan cone. -/
def toCone (sq : ValuativeCommSq f) : Bicategory.PseudoPullbackCone sq.i₂ f where
  pt := GroupoidsOver.slice sq.specK
  fst := sq.verticalMap
  snd := sq.i₁
  iso := sq.iso

/-- The apex of `toCone` is the slice of `Spec(K)`. -/
theorem toCone_pt (sq : ValuativeCommSq f) :
    sq.toCone.pt = GroupoidsOver.slice sq.specK :=
  sorry

/-- The first projection of `toCone` is the vertical morphism `j`. -/
theorem toCone_fst (sq : ValuativeCommSq f) : sq.toCone.fst = sq.verticalMap :=
  sorry

/-- The second projection of `toCone` is the top map `x`. -/
theorem toCone_snd (sq : ValuativeCommSq f) : sq.toCone.snd = sq.i₁ :=
  sorry

/-- The 2-cell of `toCone` is the 2-cell of the valuative square. -/
theorem toCone_iso (sq : ValuativeCommSq f) : sq.toCone.iso = sq.iso :=
  sorry

section ofLemmas

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] (K : Type u)
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable (structureHom : Spec (.of R) ⟶ S)
variable
  (i₁ :
    GroupoidsOver.slice
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ structureHom)) ⟶
      X)
variable (i₂ : GroupoidsOver.slice (Over.mk structureHom) ⟶ Y)
variable
  (iso :
    overMap (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl) ≫ i₂ ≅
      i₁ ≫ f)

/-- The valuation ring of `ValuativeCommSq.of` is the given ring. -/
@[simp]
theorem of_R : (of R K structureHom i₁ i₂ iso).R = R := sorry

/-- The fraction field of `ValuativeCommSq.of` is the given field. -/
@[simp]
theorem of_K : (of R K structureHom i₁ i₂ iso).K = K := sorry

/-- The structure morphism of `ValuativeCommSq.of` is the given morphism to `S`. -/
@[simp]
theorem of_structureHom : (of R K structureHom i₁ i₂ iso).structureHom = structureHom :=
  sorry

/-- The top map of `ValuativeCommSq.of` is the given morphism `Spec(K) ⟶ X`. -/
@[simp]
theorem of_i₁ : (of R K structureHom i₁ i₂ iso).i₁ = i₁ := sorry

/-- The bottom map of `ValuativeCommSq.of` is the given morphism `Spec(R) ⟶ Y`. -/
@[simp]
theorem of_i₂ : (of R K structureHom i₁ i₂ iso).i₂ = i₂ := sorry

/-- The 2-cell of `ValuativeCommSq.of` is the given isomorphism. -/
@[simp]
theorem of_iso : (of R K structureHom i₁ i₂ iso).iso = iso := sorry

end ofLemmas

end ValuativeCommSq

end AlgebraicGeometry.AlgebraicStack
