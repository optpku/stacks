/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace

/-!
# Differential of a formal object

Derivations of a complete local base induce maps to the dual numbers. Pushing forward
the first maximal-adic stage along these maps defines the differential of a formal object.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open Functor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

noncomputable section

namespace FormalObject

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- A derivation defines the algebra map to the dual numbers with scalar coefficient
given by the residue map and infinitesimal coefficient given by the derivation. -/
def toDualNumber {R : CompleteLocalAlgCat Λ k} (D : Derivation Λ R.carrier k) :
    R.carrier →ₐ[Λ] DualNumber k :=
  let formula : R.carrier → DualNumber k :=
    fun ringElement ↦ inl (algebraMap R.carrier k ringElement) + inr (D ringElement)
  let laws : formula 1 = 1 ∧
      (∀ left right, formula (left * right) = formula left * formula right) ∧
      formula 0 = 0 ∧
      (∀ left right, formula (left + right) = formula left + formula right) ∧
      (∀ scalar : Λ, formula (algebraMap Λ R.carrier scalar) =
        algebraMap Λ (DualNumber k) scalar) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext <;> simp [formula]
    · intro left right
      ext <;> simp [formula, Algebra.smul_def, algebraMap_eq_inl', mul_comm]
    · ext <;> simp [formula]
    · intro left right
      ext <;> simp [formula]
    · intro scalar
      ext
      · simp only [formula, fst_add, fst_inl, fst_inr, add_zero,
          algebraMap_eq_inl']
        change R.residueFieldIso (algebraMap Λ (ResidueField R.carrier) scalar) =
          algebraMap Λ k scalar
        exact R.residueFieldIso.commutes scalar
      · simp [formula, algebraMap_eq_inl']
  { toFun := formula
    map_one' := laws.1
    map_mul' := laws.2.1
    map_zero' := laws.2.2.1
    map_add' := laws.2.2.2.1
    commutes' := laws.2.2.2.2 }

/-- The dual-number map of a derivation has residue as its scalar coefficient and
the derivation as its infinitesimal coefficient. -/
theorem toDualNumber_apply {R : CompleteLocalAlgCat Λ k} (D : Derivation Λ R.carrier k)
    (ringElement : R.carrier) :
    toDualNumber D ringElement =
      inl (algebraMap R.carrier k ringElement) + inr (D ringElement) := rfl

/-- The dual-number map of a derivation factors through the first maximal-adic truncation
as a residue-compatible local algebra morphism. -/
def toDualNumberHom (ξ : FormalObject p) (D : Derivation Λ ξ.base.carrier k) :
    ξ.base.truncation 1 ⟶ ArtinianLocalAlgCat.dualNumber Λ k :=
  let ideal := maximalIdeal ξ.base.carrier ^ (1 + 1)
  let liftMap (vanishes : ∀ ringElement ∈ ideal, toDualNumber D ringElement = 0) :
      ArtinianLocalAlgCat.algebraHom (ξ.base.truncation 1)
        (ArtinianLocalAlgCat.dualNumber Λ k) :=
    Ideal.Quotient.liftₐ ideal (toDualNumber D) vanishes
  let laws : (∀ ringElement ∈ ideal, toDualNumber D ringElement = 0) ∧
      ∀ vanishes : ∀ ringElement ∈ ideal, toDualNumber D ringElement = 0,
        IsLocalHom (liftMap vanishes) ∧
          ∀ localHom : IsLocalHom (liftMap vanishes),
            ArtinianLocalAlgCat.residueCompat (liftMap vanishes) localHom =
              ArtinianLocalAlgCat.residueIsoHom (ξ.base.truncation 1) := by
    have residue_vanishes (ringElement : ξ.base.carrier)
        (h : ringElement ∈ maximalIdeal ξ.base.carrier) :
        algebraMap ξ.base.carrier k ringElement = 0 := by
      change ξ.base.residueFieldIso (residue ξ.base.carrier ringElement) = 0
      rw [(residue_eq_zero_iff ringElement).mpr h, map_zero]
    have vanishes : ∀ ringElement ∈ ideal, toDualNumber D ringElement = 0 := by
      have ideal_le : ideal ≤ RingHom.ker (toDualNumber D).toRingHom := by
        change maximalIdeal ξ.base.carrier ^ 2 ≤ _
        rw [pow_two]
        apply Ideal.mul_le.mpr
        intro left hleft right hright
        change toDualNumber D (left * right) = 0
        rw [map_mul, toDualNumber_apply, toDualNumber_apply,
          residue_vanishes left hleft, residue_vanishes right hright]
        simp
      exact fun ringElement h ↦ ideal_le h
    refine ⟨vanishes, ?_⟩
    intro vanishes
    refine ⟨⟨?_⟩, ?_⟩
    · intro element hunit
      obtain ⟨ringElement, rfl⟩ := Ideal.Quotient.mk_surjective element
      have scalar_unit : IsUnit (algebraMap ξ.base.carrier k ringElement) := by
        have : IsUnit (toDualNumber D ringElement).fst := isUnit_iff_isUnit_fst.mp hunit
        simpa only [toDualNumber_apply, fst_add, fst_inl, fst_inr, add_zero] using this
      have ring_unit : IsUnit ringElement := by
        apply (residue_ne_zero_iff_isUnit ringElement).mp
        intro hzero
        apply (isUnit_iff_ne_zero.mp scalar_unit)
        change ξ.base.residueFieldIso (residue ξ.base.carrier ringElement) = 0
        rw [hzero, map_zero]
      exact ring_unit.map (Ideal.Quotient.mk ideal)
    · intro localHom
      apply AlgHom.ext
      intro residueClass
      obtain ⟨element, rfl⟩ := residue_surjective residueClass
      obtain ⟨ringElement, rfl⟩ := Ideal.Quotient.mk_surjective element
      change (toDualNumber D ringElement).fst = algebraMap ξ.base.carrier k ringElement
      simp [toDualNumber_apply]
  ArtinianLocalAlgCat.Hom.of (liftMap laws.1) (laws.2 laws.1).1
    ((laws.2 laws.1).2 (laws.2 laws.1).1)

/-- Evaluation of the truncated dual-number morphism on a quotient class agrees with
evaluation of the original derivation-induced algebra map. -/
theorem toDualNumberHom_spec (ξ : FormalObject p) (D : Derivation Λ ξ.base.carrier k)
    (ringElement : ξ.base.carrier) :
    (toDualNumberHom ξ D).hom
        (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier ^ (1 + 1)) ringElement) =
      toDualNumber D ringElement := rfl

/-- Each opposite stage of a formal object lies over the opposite maximal-adic truncation. -/
theorem over_obj_op (ξ : FormalObject p) (stage : ℕ) :
    p.op.obj (Opposite.op (ξ.system.family stage)) =
      Opposite.op (ξ.base.truncation stage) := congrArg Opposite.op (ξ.over_obj stage)

/-- Push forward the first stage of a formal object along the dual-number morphism
induced by a derivation. -/
def pushforwardDualNumber (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) : F :=
  Opposite.unop (IsPreFibered.pullbackObj (over_obj_op ξ 1) (toDualNumberHom ξ D).op)

/-- The derivation-induced pushforward of a formal object lies over the dual numbers. -/
theorem pushforwardDualNumber_obj (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) :
    p.obj (pushforwardDualNumber ξ D) = ArtinianLocalAlgCat.dualNumber Λ k :=
  congrArg Opposite.unop (IsPreFibered.pullbackObj_proj (over_obj_op ξ 1)
    (toDualNumberHom ξ D).op)

/-- The differential sends a derivation of the complete local base to the isomorphism
class of the induced dual-number pushforward of the first stage. -/
def differential (ξ : FormalObject p) [IsPredeformationCategory p] :
    Derivation Λ ξ.base.carrier k → Functor.tangentSpace p :=
  fun derivation ↦ tangentSpace.mk p (Fiber.mk (pushforwardDualNumber_obj ξ derivation))

/-- The differential of a formal object is represented by its dual-number pushforward. -/
theorem differential_spec (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) :
    differential ξ D = tangentSpace.mk p (Fiber.mk (pushforwardDualNumber_obj ξ D)) := rfl

/-- A formal object has bijective differential when its derivations map bijectively
to the tangent space of the predeformation category. -/
def BijectiveDifferential (ξ : FormalObject p) [IsPredeformationCategory p] : Prop :=
  Function.Bijective (differential ξ)

end FormalObject

end
