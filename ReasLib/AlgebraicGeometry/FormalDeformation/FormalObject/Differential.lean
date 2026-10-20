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
        algebraMap Λ (DualNumber k) scalar) := sorry
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
      inl (algebraMap R.carrier k ringElement) + inr (D ringElement) := sorry

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
              ArtinianLocalAlgCat.residueIsoHom (ξ.base.truncation 1) := sorry
  ArtinianLocalAlgCat.Hom.of (liftMap laws.1) (laws.2 laws.1).1
    ((laws.2 laws.1).2 (laws.2 laws.1).1)

/-- Evaluation of the truncated dual-number morphism on a quotient class agrees with
evaluation of the original derivation-induced algebra map. -/
theorem toDualNumberHom_spec (ξ : FormalObject p) (D : Derivation Λ ξ.base.carrier k)
    (ringElement : ξ.base.carrier) :
    (toDualNumberHom ξ D).hom
        (Ideal.Quotient.mk (maximalIdeal ξ.base.carrier ^ (1 + 1)) ringElement) =
      toDualNumber D ringElement := sorry

/-- Each opposite stage of a formal object lies over the opposite maximal-adic truncation. -/
theorem over_obj_op (ξ : FormalObject p) (stage : ℕ) :
    p.op.obj (Opposite.op (ξ.system.family stage)) =
      Opposite.op (ξ.base.truncation stage) := sorry

/-- Push forward the first stage of a formal object along the dual-number morphism
induced by a derivation. -/
def pushforwardDualNumber (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) : F :=
  Opposite.unop (IsPreFibered.pullbackObj (over_obj_op ξ 1) (toDualNumberHom ξ D).op)

/-- The derivation-induced pushforward of a formal object lies over the dual numbers. -/
theorem pushforwardDualNumber_obj (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) :
    p.obj (pushforwardDualNumber ξ D) = ArtinianLocalAlgCat.dualNumber Λ k := sorry

/-- The differential sends a derivation of the complete local base to the isomorphism
class of the induced dual-number pushforward of the first stage. -/
def differential (ξ : FormalObject p) [IsPredeformationCategory p] :
    Derivation Λ ξ.base.carrier k → Functor.tangentSpace p :=
  fun derivation ↦ tangentSpace.mk p (Fiber.mk (pushforwardDualNumber_obj ξ derivation))

/-- The differential of a formal object is represented by its dual-number pushforward. -/
theorem differential_spec (ξ : FormalObject p) [IsPredeformationCategory p]
    (D : Derivation Λ ξ.base.carrier k) :
    differential ξ D = tangentSpace.mk p (Fiber.mk (pushforwardDualNumber_obj ξ D)) := sorry

/-- A formal object has bijective differential when its derivations map bijectively
to the tangent space of the predeformation category. -/
def BijectiveDifferential (ξ : FormalObject p) [IsPredeformationCategory p] : Prop :=
  Function.Bijective (differential ξ)

end FormalObject

end
