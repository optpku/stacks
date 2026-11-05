module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Map
public import ReasLib.Algebra.Category.ModuleCat.ShortComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Determinant lines of short exact rows

This leaf owns the determinant comparison attached to a short exact row of finite projective
modules.  The bundled short-complex API is the canonical owner; the presentation API below is a
thin bridge for ordinary linear maps.

@stack 0FJB
-/

noncomputable section

universe u v w x

open CategoryTheory
open scoped Module.Determinant TensorProduct

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat R)}
variable [Module.Finite R S.X₁] [Module.Projective R S.X₁]
variable [Module.Finite R S.X₂] [Module.Projective R S.X₂]
variable [Module.Finite R S.X₃] [Module.Projective R S.X₃]

/-- Lemma 15.119.2: the determinant comparison of a finite-projective short exact row is uniquely
characterized by the exterior-algebra wedge formula. -/
@[stacks 0FJB "Lemma 15.119.2: determinant comparison of a short exact row"]
theorem existsUnique_determinantTensorIso (hS : S.ShortExact) :
    ∃! γ : (det[R](S.X₁) ⊗[R] det[R](S.X₃)) ≃ₗ[R] det[R](S.X₂),
      ∀ (x₁ : det[R](S.X₁)) (x₃ : det[R](S.X₃)) (y₃ : ExteriorAlgebra R S.X₂)
        (hy₃ : ExteriorAlgebra.map S.g.hom y₃ = (x₃ : ExteriorAlgebra R S.X₃)),
          (γ (x₁ ⊗ₜ[R] x₃) : ExteriorAlgebra R S.X₂) =
            ExteriorAlgebra.map S.f.hom (x₁ : ExteriorAlgebra R S.X₁) * y₃ := sorry
-- Proof strategy: split the row using projectivity of `S.X₃`, identify `S.X₂` with
-- `S.X₁ × S.X₃`, transport the product determinant equivalence through `mapIso`, and prove
-- uniqueness by tensor-product induction together with the determinant inclusion extensionality.

/-- The canonical determinant comparison map of a short exact row. -/
@[stacks 0FJB "canonical determinant comparison of a short exact row"]
noncomputable def determinantTensorIso (hS : S.ShortExact) :
    (det[R](S.X₁) ⊗[R] det[R](S.X₃)) ≃ₗ[R] det[R](S.X₂) :=
  Classical.choose (existsUnique_determinantTensorIso hS)

/-- The determinant comparison map satisfies its defining wedge formula. -/
@[stacks 0FJB "determinant comparison wedge formula"]
theorem determinantTensorIso_spec (hS : S.ShortExact)
    (x₁ : det[R](S.X₁)) (x₃ : det[R](S.X₃)) (y₃ : ExteriorAlgebra R S.X₂)
    (hy₃ : ExteriorAlgebra.map S.g.hom y₃ = (x₃ : ExteriorAlgebra R S.X₃)) :
    (hS.determinantTensorIso (x₁ ⊗ₜ[R] x₃) : ExteriorAlgebra R S.X₂) =
      ExteriorAlgebra.map S.f.hom (x₁ : ExteriorAlgebra R S.X₁) * y₃ := sorry
-- Proof strategy: unfold `determinantTensorIso` and project the defining formula from
-- `Classical.choose_spec (existsUnique_determinantTensorIso hS)`.

/-- Lemma 15.119.3: pointwise naturality of the determinant comparison under an isomorphism of
short exact rows. The component type ascriptions keep the three projected module structures
definitionally aligned with the target row. -/
@[stacks 0FJC "pointwise naturality of determinant comparison"]
theorem determinantTensorIso_naturality_apply {T : ShortComplex (ModuleCat R)}
    [Module.Finite R T.X₁] [Module.Projective R T.X₁]
    [Module.Finite R T.X₂] [Module.Projective R T.X₂]
    [Module.Finite R T.X₃] [Module.Projective R T.X₃]
    (hS : S.ShortExact) (e : S ≅ T)
    (x₁ : det[R](S.X₁)) (x₃ : det[R](S.X₃)) :
    Module.Determinant.mapIso
        ((π₂.mapIso e).toLinearEquiv : S.X₂ ≃ₗ[R] T.X₂)
      (hS.determinantTensorIso (x₁ ⊗ₜ[R] x₃)) =
      (shortExact_of_iso e hS).determinantTensorIso
        (TensorProduct.congr
          (Module.Determinant.mapIso
            ((π₁.mapIso e).toLinearEquiv : S.X₁ ≃ₗ[R] T.X₁))
          (Module.Determinant.mapIso
            ((π₃.mapIso e).toLinearEquiv : S.X₃ ≃ₗ[R] T.X₃))
          (x₁ ⊗ₜ[R] x₃)) := sorry
-- Proof strategy: compare the two linear equivalences after inclusion into the target exterior
-- algebra; use `mapIso_ι`, functoriality of `ExteriorAlgebra.map`, the three component equations of
-- the short-complex isomorphism, and uniqueness in `existsUnique_determinantTensorIso`.

end CategoryTheory.ShortComplex.ShortExact

namespace Module.Determinant

variable {R : Type u} [CommRing R]
variable {M' : Type v} [AddCommGroup M'] [Module R M']
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {M'' : Type x} [AddCommGroup M''] [Module R M'']

/-- The universe-lifted maps attached to an exact pair still compose to zero.  This Prop-valued
law keeps the proof obligation separate from the concrete short-complex data. -/
@[stacks 0FJB "zero composite for the universe-lifted exact pair"]
theorem shortComplexOfExact_zero
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hexact : Function.Exact f g) :
    (((ULift.moduleEquiv : ULift.{max v (max w x), x} M'' ≃ₗ[R] M'').symm.toLinearMap :
          M'' →ₗ[R] ULift.{max v (max w x), x} M'').comp
        (g.comp ((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).toLinearMap :
          ULift.{max v (max w x), w} M →ₗ[R] M))).comp
      (((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).symm.toLinearMap :
          M →ₗ[R] ULift.{max v (max w x), w} M).comp
        (f.comp ((ULift.moduleEquiv : ULift.{max v (max w x), v} M' ≃ₗ[R] M').toLinearMap :
          ULift.{max v (max w x), v} M' →ₗ[R] M'))) = 0 := sorry
-- Proof strategy: reassociate the composite, cancel each adjacent `ULift.moduleEquiv` inverse
-- pair, and use `hexact.map_eq_zero` for `g.comp f`.

/-- The common-universe short complex attached to an exact pair of linear maps. -/
@[stacks 0FJB "common-universe short complex of an exact pair"]
noncomputable abbrev shortComplexOfExact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hexact : Function.Exact f g) :
    ShortComplex (ModuleCat.{max v (max w x)} R) :=
  ShortComplex.moduleCatMk
    ((((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).symm.toLinearMap :
        M →ₗ[R] ULift.{max v (max w x), w} M).comp
      (f.comp ((ULift.moduleEquiv : ULift.{max v (max w x), v} M' ≃ₗ[R] M').toLinearMap :
        ULift.{max v (max w x), v} M' →ₗ[R] M'))))
    ((((ULift.moduleEquiv : ULift.{max v (max w x), x} M'' ≃ₗ[R] M'').symm.toLinearMap :
        M'' →ₗ[R] ULift.{max v (max w x), x} M'').comp
      (g.comp ((ULift.moduleEquiv : ULift.{max v (max w x), w} M ≃ₗ[R] M).toLinearMap :
        ULift.{max v (max w x), w} M →ₗ[R] M))))
    (shortComplexOfExact_zero f g hexact)

/-- An injective, surjective, exact presentation gives a short exact complex after universe
lifting. -/
@[stacks 0FJB "exact presentation gives a short exact complex"]
theorem shortComplexOfExact_shortExact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    (shortComplexOfExact f g hexact).ShortExact := sorry
-- Proof strategy: use `ShortComplex.shortExact_iff_exact`; transport injectivity of `f`,
-- surjectivity of `g`, and `hexact` across the three `ULift.moduleEquiv` equivalences.

variable {M' : Type v} [AddCommGroup M'] [Module R M'] [Module.Finite R M']
  [Module.Projective R M']
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M]
variable {M'' : Type x} [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
  [Module.Projective R M'']

/-- The finite-projective determinant comparison for an exact pair of linear maps. -/
@[stacks 0FJB "presentation-level determinant comparison"]
theorem existsTensorIsoOfExact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    ∃ γ : (det[R](M') ⊗[R] det[R](M'')) ≃ₗ[R] det[R](M),
      ∀ (x' : det[R](M')) (x'' : det[R](M'')) (y'' : ExteriorAlgebra R M)
        (hy'' : ExteriorAlgebra.map g y'' = (x'' : ExteriorAlgebra R M'')),
          (γ (x' ⊗ₜ[R] x'') : ExteriorAlgebra R M) =
            ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * y'' := sorry
-- Proof strategy: apply `determinantTensorIso` to `shortComplexOfExact f g hexact`, transport all
-- three determinant lines along the `ULift.moduleEquiv` maps with `mapIso`, and derive the wedge
-- formula from `determinantTensorIso_spec` and functoriality of `ExteriorAlgebra.map`.

/-- The canonical determinant comparison for an exact pair of linear maps. -/
@[stacks 0FJB "canonical determinant comparison for an exact pair"]
noncomputable def tensorIsoOfExact
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g) :
    (det[R](M') ⊗[R] det[R](M'')) ≃ₗ[R] det[R](M) :=
  Classical.choose (existsTensorIsoOfExact f g hf hg hexact)

/-- The presentation-level determinant comparison satisfies the wedge formula. -/
@[stacks 0FJB "presentation determinant comparison wedge formula"]
theorem tensorIsoOfExact_spec
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'') (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g)
    (x' : det[R](M')) (x'' : det[R](M'')) (y'' : ExteriorAlgebra R M)
    (hy'' : ExteriorAlgebra.map g y'' = (x'' : ExteriorAlgebra R M'')) :
    (tensorIsoOfExact f g hf hg hexact (x' ⊗ₜ[R] x'') : ExteriorAlgebra R M) =
      ExteriorAlgebra.map f (x' : ExteriorAlgebra R M') * y'' := sorry
-- Proof strategy: unfold `tensorIsoOfExact` and project the formula from
-- `Classical.choose_spec (existsTensorIsoOfExact f g hf hg hexact)`.

end Module.Determinant

end
