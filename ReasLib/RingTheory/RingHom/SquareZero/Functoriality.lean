/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import ReasLib.RingTheory.RingHom.SquareZero.Diagram
public import ReasLib.RingTheory.RingHom.SquareZero.AlgebraExtension

/-!
# Functoriality of square-zero algebra extension classes

Coefficient change and restriction of scalars transport naive cotangent Ext¹ classes.
A compatible map of square-zero algebra extensions exists precisely when their
transported classes agree.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension

namespace RingHom.SquareZeroExtension

section Precomp

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The canonical B-linear map J/J² → K/K² induced by the default generator
hom from the self-presentation of B over A to that of C over A. -/
def extOneNaiveCotangent_precomp :
    (Generators.self A B).toExtension.Cotangent →ₗ[B]
      (Generators.self A C).toExtension.Cotangent :=
  Cotangent.map
    (Hom.toExtensionHom (defaultHom (Generators.self A B) (Generators.self A C)))

/-- The canonical cotangent precomposition map acts by the default generator hom. -/
theorem extOneNaiveCotangent_precomp_apply
    (x : (Generators.self A B).toExtension.Cotangent) :
    extOneNaiveCotangent_precomp x =
      Cotangent.map
        (Hom.toExtensionHom (defaultHom (Generators.self A B) (Generators.self A C)))
        x := sorry

end Precomp

section Map

variable {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- Covariant change of coefficients Ext¹_B(NL_{B/A}, M) → Ext¹_B(NL_{B/A}, N)
along a B-linear map c : M →ₗ[B] N. -/
def extOneNaiveCotangent_map (c : M →ₗ[B] N) (ξ : extOneNaiveCotangent A B M) :
    extOneNaiveCotangent A B N :=
  Quotient.liftOn ξ (fun f ↦ extOneNaiveCotangent_mk A B N (c ∘ₗ f)) (by
    intro f g h
    apply (Submodule.Quotient.eq _).mpr
    change
      (LinearMap.range (LinearMap.lcomp B M
        (Generators.self A B).toExtension.cotangentComplex)).quotientRel f g at h
    rw [Submodule.quotientRel_def] at h
    rcases h with ⟨k, hk⟩
    refine ⟨LinearMap.llcomp B _ M N c k, ?_⟩
    ext x
    simp only [LinearMap.lcomp_apply, LinearMap.llcomp_apply, LinearMap.sub_apply,
      LinearMap.comp_apply]
    rw [← map_sub, ← LinearMap.sub_apply, ← hk]
    rfl)

/-- Coefficient change on a Hom representative is postcomposition by c. -/
theorem extOneNaiveCotangent_map_mk (c : M →ₗ[B] N)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] M) :
    extOneNaiveCotangent_map c (extOneNaiveCotangent_mk A B M f) =
      extOneNaiveCotangent_mk A B N (c ∘ₗ f) := sorry

/-- The zero Ext¹ class is sent to zero under coefficient change. -/
theorem extOneNaiveCotangent_map_zero (c : M →ₗ[B] N) :
    extOneNaiveCotangent_map c (0 : extOneNaiveCotangent A B M) = 0 := sorry

end Map

section Comap

/-- Restriction along B → C then precomposition with NL_{B/A} → NL_{C/A},
as a map Ext¹_C(NL_{C/A}, N) → Ext¹_B(NL_{B/A}, N). -/
def extOneNaiveCotangent_comap (B : Type u) {A C N : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]
    (ζ : extOneNaiveCotangent A C N) : extOneNaiveCotangent A B N :=
  Quotient.liftOn ζ
    (fun f ↦
        extOneNaiveCotangent_mk A B N
        (LinearMap.restrictScalars B f ∘ₗ extOneNaiveCotangent_precomp))
    (by
      intro f g h
      apply (Submodule.Quotient.eq _).mpr
      change
        (LinearMap.range (LinearMap.lcomp C N
          (Generators.self A C).toExtension.cotangentComplex)).quotientRel f g at h
      rw [Submodule.quotientRel_def] at h
      rcases h with ⟨k, hk⟩
      refine ⟨LinearMap.restrictScalars B k ∘ₗ
        CotangentSpace.map
          (Hom.toExtensionHom
            (defaultHom (Generators.self A B) (Generators.self A C))), ?_⟩
      ext x
      simp only [LinearMap.lcomp_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.coe_restrictScalars]
      rw [← LinearMap.sub_apply, ← hk]
      rw [CotangentSpace.map_cotangentComplex]
      rfl)

/-- Restriction on Hom representatives restricts scalars along B → C and
precomposes with the canonical cotangent map. -/
theorem extOneNaiveCotangent_comap_mk (B : Type u) {A C N : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]
    (f : (Generators.self A C).toExtension.Cotangent →ₗ[C] N) :
    extOneNaiveCotangent_comap B (extOneNaiveCotangent_mk A C N f) =
      extOneNaiveCotangent_mk A B N
        (LinearMap.restrictScalars B f ∘ₗ extOneNaiveCotangent_precomp) := sorry

/-- The zero Ext¹ class is sent to zero under restriction and precomposition. -/
theorem extOneNaiveCotangent_comap_zero (B : Type u) {A C N : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N] :
    extOneNaiveCotangent_comap B (0 : extOneNaiveCotangent A C N) = 0 := sorry

end Comap

section AlgebraMap

variable {A B C M N : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup N] [Module C N] [Module B N] [Module A N]
variable [IsScalarTower B C N] [IsScalarTower A C N] [IsScalarTower A B N]

namespace RelativeDiagram

/-- The identity-base connecting diagram of two square-zero A-algebra extensions,
with g = algebraMap B C and ν the additive map underlying c. -/
def ofAlgebraMap (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _)
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    RelativeDiagram SB SC where
  t' := RingHom.id A
  t := RingHom.id A
  g := algebraMap B C
  ν := c.toAddMonoidHom
  map_smul_ν := sorry
  comm_base := sorry
  comm_alg := sorry
  comm_kernel := sorry

/-- The identity-base diagram has identity maps on A, the algebra map B → C,
and the additive map underlying c on kernels. -/
theorem ofAlgebraMap_spec (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _)
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    (ofAlgebraMap c SB SC).t' = RingHom.id A ∧
      (ofAlgebraMap c SB SC).t = RingHom.id A ∧
      (ofAlgebraMap c SB SC).g = algebraMap B C ∧
      (ofAlgebraMap c SB SC).ν = c.toAddMonoidHom := sorry

end RelativeDiagram

/-- A compatible map between square-zero A-algebra extensions exists if and only
if coefficient change and restriction transport their classes to the same
element of Ext¹_B(NL_{B/A}, N). -/
theorem fittingMap_nonempty_iff (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _)
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _) :
    Nonempty (FittingMap (RelativeDiagram.ofAlgebraMap c SB SC)) ↔
      extOneNaiveCotangent_map c ((algebraExtensionEquiv A B M).symm (isoClassMk SB)) =
        extOneNaiveCotangent_comap B
          ((algebraExtensionEquiv A C N).symm (isoClassMk SC)) := sorry

end AlgebraMap

end SquareZeroExtension

end RingHom
