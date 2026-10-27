/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber

/-!
# Comparison maps of field-valued fibres

Commutative squares and factorizations of field-valued points induce canonical
maps of scheme-theoretic fibres, characterized by their two projections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A commutative square induces a cone over the target morphism and the
mapped field-valued point. -/
theorem fiberOver_mapSquare_condition {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (hw : fst ≫ f = g ≫ a) :
    (fieldFiberι g p ≫ fst) ≫ f = fieldFiberToSpec g p ≫ (p.map a).hom :=
  calc
    (fieldFiberι g p ≫ fst) ≫ f = fieldFiberι g p ≫ (fst ≫ f) := by
      simp only [Category.assoc]
    _ = fieldFiberι g p ≫ (g ≫ a) := by rw [hw]
    _ = (fieldFiberι g p ≫ g) ≫ a := by simp only [Category.assoc]
    _ = (fieldFiberToSpec g p ≫ p.hom) ≫ a := by rw [fieldFiberι_comp]
    _ = fieldFiberToSpec g p ≫ (p.hom ≫ a) := by simp only [Category.assoc]
    _ = fieldFiberToSpec g p ≫ (p.map a).hom := by rfl

/-- The morphism of fibres over a field-valued point induced by a commutative
square of algebraic spaces. -/
def fiberOver_mapSquare {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (hw : fst ≫ f = g ≫ a) :
    fieldFiber g p ⟶ fieldFiber f (p.map a) :=
  pullback.lift (fieldFiberι g p ≫ fst) (fieldFiberToSpec g p)
    (fiberOver_mapSquare_condition f a fst g p hw)

/-- The fibre comparison induced by a commutative square commutes with the
projection to the source and preserves the projection to the representative spectrum. -/
theorem fiberOver_mapSquare_spec {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (hw : fst ≫ f = g ≫ a) :
    fiberOver_mapSquare f a fst g p hw ≫ fieldFiberι f (p.map a) =
        fieldFiberι g p ≫ fst ∧
      fiberOver_mapSquare f a fst g p hw ≫ fieldFiberToSpec f (p.map a) =
        fieldFiberToSpec g p := by
  constructor
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

/-- The fibre comparison along a cartesian square is an isomorphism. -/
theorem isIso_fiberOver_mapSquare {S : Scheme.{u}} {Y Y' V W : AlgebraicSpace S}
    (f : Y ⟶ W) (a : V ⟶ W) (fst : Y' ⟶ Y) (g : Y' ⟶ V) (p : FieldValuedPoint V)
    (hw : fst ≫ f = g ≫ a)
    (h : IsPullback fst g f a) : IsIso (fiberOver_mapSquare f a fst g p hw) :=
  sorry

/-- A factorization of field-valued points induces a cone over a morphism
and the target field-valued point. -/
theorem fiberOver_factor_condition {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {p q : FieldValuedPoint X} (φ : p.Factorization q) :
    fieldFiberι f p ≫ f =
      (fieldFiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure) ≫ q.hom :=
  calc
    fieldFiberι f p ≫ f = fieldFiberToSpec f p ≫ p.hom := fieldFiberι_comp f p
    _ = fieldFiberToSpec f p ≫
        (ofOverHomMk φ.schemeHom φ.fac_structure ≫ q.hom) :=
      congrArg (fun k ↦ fieldFiberToSpec f p ≫ k) φ.fac_hom.symm
    _ = (fieldFiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure) ≫ q.hom := by
      simp only [Category.assoc]

/-- The morphism of fibres of a fixed morphism induced by a factorization
of field-valued points of its target. -/
def fiberOver_factor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    {p q : FieldValuedPoint X} (φ : p.Factorization q) :
    fieldFiber f p ⟶ fieldFiber f q :=
  pullback.lift (fieldFiberι f p)
    (fieldFiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure)
    (fiberOver_factor_condition f φ)

/-- The fibre comparison induced by a factorization preserves the source
projection and induces the specified morphism of representative spectra. -/
theorem fiberOver_factor_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {p q : FieldValuedPoint X} (φ : p.Factorization q) :
    fiberOver_factor f φ ≫ fieldFiberι f q = fieldFiberι f p ∧
      fiberOver_factor f φ ≫ fieldFiberToSpec f q =
        fieldFiberToSpec f p ≫ ofOverHomMk φ.schemeHom φ.fac_structure := by
  constructor
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

/-- A factorization that is an isomorphism on representative spectra induces
an isomorphism of fibres. -/
theorem isIso_fiberOver_factor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) {p q : FieldValuedPoint X} (φ : p.Factorization q)
    [IsIso φ.schemeHom] : IsIso (fiberOver_factor f φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
