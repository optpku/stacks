module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.LinearAlgebra.TensorProduct.Domination
public import ReasLib.LinearAlgebra.TensorProduct.PushoutQuotient
public import ReasLib.LinearAlgebra.UniversallyInjective
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Criteria

/-!
# Tensor-kernel domination and pushouts

@stack 0AUM
@stack 059D

The tensor-specific pushout kernel calculation lives in
`ModuleCat.PushoutQuotient.injective_pushoutInr_rTensor_iff`. This file applies that reusable
criterion to tensor-kernel domination and records the finite-presentation factorization theorem.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace LinearMap.Dominates

variable {R : Type u} [CommRing R]
variable {M N P : Type v}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- Lemma 10.88.4, tag `0AUM`: tensor-kernel domination is equivalent to
universal injectivity of the right leg in the corresponding pushout square. -/
@[stacks 0AUM]
theorem iff_universallyInjective_pushoutInr (f : M →ₗ[R] N) (g : M →ₗ[R] P) :
    g.Dominates f ↔
      LinearMap.UniversallyInjective.{u, v, v, max u v}
        ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom) := by
  constructor
  · intro hdom Q _ _
    exact
      (ModuleCat.PushoutQuotient.injective_pushoutInr_rTensor_iff
        (Q := Q) f g).2 (hdom Q)
  · intro huniv Q _ _
    exact
      (ModuleCat.PushoutQuotient.injective_pushoutInr_rTensor_iff
        (Q := Q) f g).1
        (huniv Q (Module.addCommMonoidToAddCommGroup R (M := Q)) inferInstance)

/-- Lemma 10.88.5, tag `059D`: if the cokernel of `f` is finitely presented,
then `g` tensor-kernel dominates `f` exactly when `g` factors through `f`. -/
@[stacks 059D]
theorem iff_factorsThrough (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    [Module.FinitePresentation R (N ⧸ LinearMap.range f)] :
    g.Dominates f ↔ ∃ h : N →ₗ[R] P, g = h.comp f := by
  let F : ModuleCat.of R M ⟶ ModuleCat.of R N := ModuleCat.ofHom f
  let G : ModuleCat.of R M ⟶ ModuleCat.of R P := ModuleCat.ofHom g
  let b : ModuleCat.of R P ⟶ pushout F G := pushout.inr F G
  constructor
  · intro hdom
    have hb : LinearMap.UniversallyInjective.{u, v, v, max u v} b.hom :=
      (iff_universallyInjective_pushoutInr f g).mp hdom
    -- Local instance justification (canonical transport): use the standard cokernel quotient
    -- equivalence to transport the hypothesis on `N / range f`.
    letI : Module.FinitePresentation R ((cokernel F : ModuleCat.{v} R) : Type v) :=
      Module.FinitePresentation.of_equiv
        (ModuleCat.cokernelIsoRangeQuotient F).symm.toLinearEquiv
    let sq : IsPushout F G (pushout.inl F G) b := IsPushout.of_hasPushout F G
    let cokerMap : cokernel F ⟶ cokernel b :=
      cokernel.map F b G (pushout.inl F G) sq.w
    -- Local instance justification (property witness): the cokernel comparison in a pushout is
    -- an isomorphism, and the splitting criterion consumes this fact through typeclass search.
    letI : IsIso cokerMap := isIso_cokernel_map_of_isPushout sq
    -- Local instance justification (canonical transport): move finite presentation across the
    -- canonical cokernel comparison isomorphism.
    letI : Module.FinitePresentation R ((cokernel b : ModuleCat.{v} R) : Type v) :=
      Module.FinitePresentation.of_equiv (asIso cokerMap).toLinearEquiv
    let S : ShortComplex (ModuleCat.{v} R) :=
      ShortComplex.mk b (cokernel.π b) (cokernel.condition b)
    have hS : S.UniversallyExact := by
      refine ⟨?_, hb⟩
      exact
        { exact := ShortComplex.exact_cokernel b
          mono_f := (ModuleCat.mono_iff_injective b).mpr hb.injective
          epi_g := inferInstance }
    obtain ⟨s⟩ :=
      (CategoryTheory.ShortComplex.UniversallyExact.iff_nonempty_splitting
        (S := S)).mp hS
    let h : N →ₗ[R] P := (pushout.inl F G ≫ s.r).hom
    refine ⟨h, ?_⟩
    have hcat : F ≫ (pushout.inl F G ≫ s.r) = G := by
      rw [← Category.assoc, pushout.condition, Category.assoc, s.f_r,
        Category.comp_id]
    exact (congrArg ModuleCat.Hom.hom hcat).symm
  · exact LinearMap.dominates_of_factorization

end LinearMap.Dominates
