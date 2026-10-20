/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import ReasLib.Algebra.Ring.CharZero.ULift
public import ReasLib.AlgebraicGeometry.Scheme.EtaleEquivalenceRelation

/-!
# Affine line modulo integer translation

The affine line over a characteristic-zero field carries the translation action of
`ℤ`, with étale equivalence relation `R = ∐_{n : ℤ} U` and `j(n, x) = (x + n, x)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AffineSpace
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient

/-- The base scheme `S = Spec k`. -/
abbrev base (k : Type u) [Field k] [CharZero k] : Scheme.{u} :=
  Spec (CommRingCat.of k)

/-- The base scheme is the spectrum of `k`. -/
theorem base_eq (k : Type u) [Field k] [CharZero k] :
    base k = Spec (CommRingCat.of k) := sorry

/-- The affine line `U = 𝔸¹_k` as a scheme over `S`. -/
def cover (k : Type u) [Field k] [CharZero k] : Over (base k) :=
  asOver (𝔸(ULift.{u} (Fin 1); base k)) (base k)

/-- The underlying scheme of the cover is the relative affine line. -/
theorem cover_left (k : Type u) [Field k] [CharZero k] :
    (cover k).left = 𝔸(ULift.{u} (Fin 1); base k) := sorry

/-- The structure morphism of the cover is the canonical projection of affine space. -/
theorem cover_hom (k : Type u) [Field k] [CharZero k] :
    (cover k).hom = 𝔸(ULift.{u} (Fin 1); base k) ↘ base k := sorry

/-- The affine line over a field is quasi-compact. -/
instance instCompactSpace_cover (k : Type u) [Field k] [CharZero k] :
    CompactSpace (cover k).left := sorry

/-- Translation by `n` on the underlying affine line, sending a point `x` to `x + n`. -/
abbrev translateLeft (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    𝔸(ULift.{u} (Fin 1); base k) ⟶ 𝔸(ULift.{u} (Fin 1); base k) :=
  homOfVector (𝔸(ULift.{u} (Fin 1); base k) ↘ base k) fun i : ULift.{u} (Fin 1) ↦
    coord (base k) i + (n : Γ(𝔸(ULift.{u} (Fin 1); base k), ⊤))

/-- Translation by `n` commutes with the structure morphism of the affine line. -/
theorem translate_w (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    translateLeft k n ≫ 𝔸(ULift.{u} (Fin 1); base k) ↘ base k =
      𝔸(ULift.{u} (Fin 1); base k) ↘ base k := sorry

/-- Translation by `n` as an automorphism of the affine line over `S`. -/
def translate (k : Type u) [Field k] [CharZero k] (n : ℤ) : cover k ⟶ cover k :=
  (translateLeft k n).asOver (base k)

/-- The underlying scheme morphism of `translate k n` is `translateLeft k n`. -/
theorem translate_left (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    (translate k n).left = translateLeft k n := sorry

/-- Translation by zero is the identity. -/
theorem translate_zero (k : Type u) [Field k] [CharZero k] :
    translate k 0 = 𝟙 (cover k) := sorry

/-- Translation is a homomorphism from `(ℤ, +)` to automorphisms of the cover. -/
theorem translate_add (k : Type u) [Field k] [CharZero k] (m n : ℤ) :
    translate k (m + n) = translate k m ≫ translate k n := sorry

/-- Translation by `n` is inverted by translation by `-n`. -/
theorem translate_neg (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    translate k n ≫ translate k (-n) = 𝟙 (cover k) := sorry

/-- The `n`-th summand of the relation scheme is a copy of the affine line. -/
def relationComponent (k : Type u) [Field k] [CharZero k] : ℤ → Over (base k) :=
  fun _ ↦ cover k

/-- Every relation summand is the cover `U`. -/
theorem relationComponent_eq (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    relationComponent k n = cover k := sorry

/-- The component of `j` on the summand indexed by `n` is `(x ↦ x + n, id)`. -/
def relationComponentHom (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    relationComponent k n ⟶ cover k ⨯ cover k :=
  prod.lift (translate k n) (𝟙 (cover k))

/-- The component map on the `n`-th summand is the pair `(translate n, 𝟙)`. -/
theorem relationComponentHom_eq (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    relationComponentHom k n = prod.lift (translate k n) (𝟙 (cover k)) := sorry

/-- The relation scheme `R = ∐_{n : ℤ} U` as an object over `S`. -/
def relationOver (k : Type u) [Field k] [CharZero k] : Over (base k) :=
  ∐ relationComponent k

/-- The underlying object of `relationOver` is the coproduct of copies of `U`. -/
theorem relationOver_eq (k : Type u) [Field k] [CharZero k] :
    relationOver k = ∐ relationComponent k := sorry

/-- The morphism `j : R ⟶ U ×_S U`, whose `n`-th component is `(x ↦ x + n, id)`. -/
def relationHom (k : Type u) [Field k] [CharZero k] :
    relationOver k ⟶ cover k ⨯ cover k :=
  Sigma.desc (relationComponentHom k)

/-- The defining map of the relation is the coproduct fold of the component maps. -/
theorem relationHom_eq (k : Type u) [Field k] [CharZero k] :
    relationHom k = Sigma.desc (relationComponentHom k) := sorry

/-- The pre-relation on `U` over `S` with source `R` and defining map `j`. -/
def preRelation (k : Type u) [Field k] [CharZero k] : PreRelation (cover k) :=
  PreRelation.ofHom (relationHom k)

/-- The defining arrow of `preRelation k` is `relationHom k`. -/
theorem preRelation_hom (k : Type u) [Field k] [CharZero k] :
    (preRelation k).hom = relationHom k := sorry

/-- The first projection of the relation, restricted to the `n`-th summand, is translation by `n`. -/
theorem preRelation_t_ι (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    Sigma.ι (relationComponent k) n ≫ (preRelation k).t = translate k n := sorry

/-- The second projection of the relation, restricted to the `n`-th summand, is the identity. -/
theorem preRelation_s_ι (k : Type u) [Field k] [CharZero k] (n : ℤ) :
    Sigma.ι (relationComponent k) n ≫ (preRelation k).s = 𝟙 (cover k) := sorry

/-- Integer translation on the affine line over a characteristic-zero field is an étale
equivalence relation. -/
instance instIsEtaleEquivalenceRelation_preRelation (k : Type u) [Field k] [CharZero k] :
    (preRelation k).IsEtaleEquivalenceRelation := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineQuotient
