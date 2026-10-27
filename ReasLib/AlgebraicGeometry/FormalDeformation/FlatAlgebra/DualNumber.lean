/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.AdicCompletion

/-!
# Trivial dual-number lift of a ring deformation

The residue-fibre slice projection of `Def_P` and the trivial `k[ε]`-algebra
`P[ε] = DualNumber P`.
-/

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt

noncomputable section

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- `deformationForget` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (P : Type u) [CommRing P] [Algebra k P] :
    deformationForget Λ k P =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget := rfl

/-- The slice projection of `Def_P` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (P : Type u) [CommRing P] [Algebra k P] :
    IsPredeformationCategory (deformationForget Λ k P) :=
  CategoryTheory.Functor.instIsPredeformationCategory_overForget
    (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) (residueObj Λ k P)

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op
    (P : Type u) [CommRing P] [Algebra k P] :
    IsFibered.InGroupoids (deformationForget Λ k P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The constant inclusion of the residue field in its dual numbers is local. -/
private theorem residueToDualNumber_isLocalHom :
    IsLocalHom (inlAlgHom Λ k k) := sorry

/-- The constant inclusion preserves the chosen residue-field identifications. -/
private theorem residueToDualNumber_residue_compat :
    residueCompat (A := residue Λ k) (B := dualNumber Λ k)
      (inlAlgHom Λ k k) (residueToDualNumber_isLocalHom Λ k) =
        residueIsoHom (residue Λ k) := sorry

/-- The constant inclusion from the residue-field object into its dual numbers. -/
def residueToDualNumber : residue Λ k ⟶ dualNumber Λ k :=
  ArtinianLocalAlgCat.Hom.of (inlAlgHom Λ k k)
    (by exact residueToDualNumber_isLocalHom Λ k) (by exact residueToDualNumber_residue_compat Λ k)

/-- The constant inclusion sends a scalar to its constant dual number. -/
theorem residueToDualNumber_apply (a : (residue Λ k).carrier) :
    (residueToDualNumber Λ k).hom a = inl (a : k) := rfl

/-- The coefficientwise ring map from dual numbers over a field to dual numbers over an
algebra over that field. -/
def dualNumberRingHom (P : Type u) [CommRing P] [Algebra k P] :
    (dualNumber Λ k).carrier →+* DualNumber P :=
  (DualNumber.lift ⟨(Algebra.ofId k (DualNumber P), DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ ↦ DualNumber.commute_eps_left _⟩).toRingHom

/-- The coefficient ring map applies the algebra map to both coordinates. -/
theorem dualNumberRingHom_apply (P : Type u) [CommRing P] [Algebra k P]
    (x : (dualNumber Λ k).carrier) :
    dualNumberRingHom Λ k P x = ⟨algebraMap k P x.fst, algebraMap k P x.snd⟩ := by
  change inl (algebraMap k P x.fst) +
    inl (algebraMap k P x.snd) * DualNumber.eps = _
  ext <;> simp only [fst_add, fst_inl, fst_mul, DualNumber.fst_eps, mul_zero,
    add_zero, snd_add, snd_inl, DualNumber.snd_mul, DualNumber.snd_eps,
    mul_one, zero_add, fst_mk, snd_mk]

/-- `P[ε]` is a `k[ε]`-algebra via the coefficientwise algebra map. -/
instance instAlgebra_trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    Algebra (dualNumber Λ k).carrier (DualNumber P) :=
  (dualNumberRingHom Λ k P).toAlgebra

/-- `P[ε]` is flat as a module over `k[ε]`. -/
instance instModuleFlat_trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    Module.Flat (dualNumber Λ k).carrier (DualNumber P) := sorry

/-- The trivial dual-number object `(k[ε], P[ε])` of `FlatAlgebraCat`. -/
def trivialDeformationObj (P : Type u) [CommRing P] [Algebra k P] : FlatAlgebraCat Λ k :=
  of (dualNumber Λ k) (DualNumber P)

/-- The base of `trivialDeformationObj` is `k[ε]`. -/
theorem trivialDeformationObj_base (P : Type u) [CommRing P] [Algebra k P] :
    (trivialDeformationObj Λ k P).base = dualNumber Λ k := rfl

/-- The underlying algebra of `trivialDeformationObj` is `DualNumber P`. -/
theorem trivialDeformationObj_carrier (P : Type u) [CommRing P] [Algebra k P] :
    (trivialDeformationObj Λ k P).algebra = DualNumber P := rfl

/-- The trivial dual-number deformation of `x0 = (k, P)` in the fibre of `forget`. -/
def trivialDeformation (P : Type u) [CommRing P] [Algebra k P] :
    forget.Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : forget.obj (trivialDeformationObj Λ k P) = dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialDeformationObj`. -/
theorem trivialDeformation_obj (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (trivialDeformation Λ k P) = trivialDeformationObj Λ k P := rfl

/-- The first projection on the trivial deformation commutes with the coefficient maps. -/
private theorem trivialDeformationToResidue_commutes
    (P : Type u) [CommRing P] [Algebra k P] :
    ((fstHom P P P).toRingHom).comp
        (algebraMap (trivialDeformationObj Λ k P).base.carrier
          (trivialDeformationObj Λ k P).algebra) =
      (algebraMap (ofResidue Λ k P).base.carrier (ofResidue Λ k P).algebra).comp
        (ArtinianLocalAlgCat.dualNumberToResidue Λ k).hom.toRingHom := sorry

/-- The first projection on the trivial deformation induces a base-change isomorphism. -/
private theorem trivialDeformationToResidue_isIsoTensor
    (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (canonicalTensorMap
      (Q := trivialDeformationObj Λ k P) (P := ofResidue Λ k P)
      (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (fstHom P P P).toRingHom
      (trivialDeformationToResidue_commutes Λ k P)) := sorry

/-- The morphism `(k[ε], P[ε]) ⟶ (k, P)` over the coefficient projection `k[ε] ⟶ k`. -/
def trivialDeformationToResidue (P : Type u) [CommRing P] [Algebra k P] :
    trivialDeformationObj Λ k P ⟶ ofResidue Λ k P :=
  Hom.of (ArtinianLocalAlgCat.dualNumberToResidue Λ k) (fstHom P P P).toRingHom
    (by exact trivialDeformationToResidue_commutes Λ k P)
    (by exact trivialDeformationToResidue_isIsoTensor Λ k P)

/-- The base map of `trivialDeformationToResidue` is `dualNumberToResidue`. -/
theorem trivialDeformationToResidue_base (P : Type u) [CommRing P] [Algebra k P] :
    forget.map (trivialDeformationToResidue Λ k P) = ArtinianLocalAlgCat.dualNumberToResidue Λ k := rfl

/-- The constant inclusions commute with the coefficient algebra maps. -/
private theorem trivialPushforward_commutes (P : Type u) [CommRing P] [Algebra k P] :
    (inlHom P P).comp (algebraMap (ofResidue Λ k P).base.carrier (ofResidue Λ k P).algebra) =
      (algebraMap (trivialDeformationObj Λ k P).base.carrier (trivialDeformationObj Λ k P).algebra).comp
        (residueToDualNumber Λ k).hom.toRingHom := sorry

/-- The constant inclusion on the trivial deformation induces a base-change isomorphism. -/
private theorem trivialPushforward_isIsoTensor
    (P : Type u) [CommRing P] [Algebra k P] :
    Function.Bijective (canonicalTensorMap
      (Q := ofResidue Λ k P) (P := trivialDeformationObj Λ k P)
      (residueToDualNumber Λ k) (inlHom P P)
      (trivialPushforward_commutes Λ k P)) := sorry

/-- The morphism `(k, P) ⟶ (k[ε], P[ε])` over the inclusion `k ⟶ k[ε]`. -/
def trivialPushforward (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (residueObj Λ k P) ⟶
      Fiber.fiberInclusion.obj (trivialDeformation Λ k P) :=
  Hom.of (residueToDualNumber Λ k) (inlHom P P)
    (by exact trivialPushforward_commutes Λ k P) (by exact trivialPushforward_isIsoTensor Λ k P)

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (P : Type u) [CommRing P] [Algebra k P] :
    forget.map (trivialPushforward Λ k P) = residueToDualNumber Λ k := rfl

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    (P : Type u) [CommRing P] [Algebra k P] :
    forget.IsStronglyCocartesian (residueToDualNumber Λ k) (trivialPushforward Λ k P) := sorry

/-- The trivial deformation as an object of the residue-fibre slice `Def_P`. -/
def trivialDeformationOver (P : Type u) [CommRing P] [Algebra k P] :
    deformationCategory Λ k P :=
  Over.mk (trivialDeformationToResidue Λ k P)

/-- The trivial deformation in the dual-number fibre of `deformationForget`. -/
def trivialDeformationFiber (P : Type u) [CommRing P] [Algebra k P] :
    (deformationForget Λ k P).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k P).obj (trivialDeformationOver Λ k P) = dualNumber Λ k)

/-- The underlying Over-object of `trivialDeformationFiber` is `trivialDeformationOver`. -/
theorem trivialDeformationFiber_obj (P : Type u) [CommRing P] [Algebra k P] :
    Fiber.fiberInclusion.obj (trivialDeformationFiber Λ k P) =
      trivialDeformationOver Λ k P := rfl

end FlatAlgebraCat
