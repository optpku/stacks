module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_12_3
public import stacks_project.Chap90.Lemma_90_20_3
public import stacks_project.Chap93.Lemma_93_8_2
public import stacks_project.Chap93.Lemma_93_8_10_AdicCompletion

/-!
# Smoothness of completion of ring deformation categories

If `k → P` is of finite type and `Spec P ⟶ Spec k` is smooth on the complement
of `zeroLocus J`, then `adicCompletionBasedFunctor Λ k P J` is smooth and
induces a bijection on tangent spaces.
-/

@[expose] public section

open CategoryTheory Functor
open Algebra
open PrimeSpectrum

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {P : Type u} [CommRing P] [Algebra k P]

namespace FlatAlgebraCat

/-- The slice projection `deformationForget Λ k P` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget (P : Type u) [CommRing P]
    [Algebra k P] : IsPredeformationCategory (deformationForget Λ k P) :=
  inferInstanceAs
    (IsPredeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙
        (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)))

variable (Λ k) in
/-- The Lemma 93.8.10 based functor `Def_P ⥤ᵇ Def_{AdicCompletion J P}` for a
finite type `k`-algebra. -/
noncomputable def adicCompletionBasedFunctorOfFiniteType [Algebra.FiniteType k P]
    (J : Ideal P) :=
  -- Local instance justification (proof-local temporary data): finite type over a field supplies the Noetherian hypothesis of `adicCompletionBasedFunctor`; `k` is not determined from `P`, so this cannot be a global instance.
  letI := Algebra.FiniteType.isNoetherianRing k P
  adicCompletionBasedFunctor Λ k P J

/-- Completing a finite type deformation does not change the Artinian local base. -/
theorem adicCompletionBasedFunctorOfFiniteType_obj_base [Algebra.FiniteType k P]
    (J : Ideal P) (ξ : deformationCategory Λ k P) :
    ((adicCompletionBasedFunctorOfFiniteType Λ k J).toFunctor.obj ξ).left.base =
      ξ.left.base :=
  sorry

/-- Lemma 93.12.5 (1)
In Example 93.8.1, let `P` be a finite type `k`-algebra and let `J ⊆ P` be an
ideal such that `Spec P ⟶ Spec k` is smooth on the complement of `zeroLocus J`.
Then the functor `Def_P ⟶ Def_{AdicCompletion J P}` of Lemma 93.8.10, as the
based functor `adicCompletionBasedFunctor Λ k P J`, is smooth. -/
@[stacks 0DZ5]
theorem isSmooth_adicCompletionBasedFunctor [Algebra.FiniteType k P] (J : Ideal P)
    (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    BasedFunctor.IsSmooth (adicCompletionBasedFunctorOfFiniteType Λ k J) := sorry

/-- Lemma 93.12.5 (2)
In Example 93.8.1, let `P` be a finite type `k`-algebra and let `J ⊆ P` be an
ideal such that `Spec P ⟶ Spec k` is smooth on the complement of `zeroLocus J`.
Then the differential of `adicCompletionBasedFunctor Λ k P J` is bijective on
tangent spaces. -/
@[stacks 0DZ5]
theorem bijective_differential_adicCompletionBasedFunctor [Algebra.FiniteType k P]
    (J : Ideal P) (hsmooth : (zeroLocus (J : Set P))ᶜ ⊆ smoothLocus k P) :
    Function.Bijective
      (BasedFunctor.differential (adicCompletionBasedFunctorOfFiniteType Λ k J)) :=
  sorry

end FlatAlgebraCat
