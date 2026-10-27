/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import ReasLib.CategoryTheory.Linear.Functor
public import ReasLib.RingTheory.AlgHom.Lifting
public import ReasLib.RingTheory.RingHom.SquareZero.Solution

/-! # Polynomial presentation obstruction modules

The cotangent Hom cokernel, evaluation obstruction classes, and changes of coefficients.
-/

@[expose] public section

set_option backward.privateInPublic true
open CategoryTheory Algebra Algebra.Generators Algebra.Extension MvPolynomial
noncomputable section
universe u
namespace Algebra.NaiveCotangent.Obstruction

/-- Homomorphisms from `J/J²` into an `A`-module, linear over the presented ring along `φ`. -/
abbrev relationHom {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] : Type u :=
  (Generators.naive (I := J)).toExtension.Cotangent →ₛₗ[φ.toRingHom] N

/-- Homomorphisms from the free module on the presentation generators into an `A`-module. -/
abbrev generatorHom {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] : Type u :=
  ((ι →₀ MvPolynomial ι Λ ⧸ J) →ₛₗ[φ.toRingHom] N)

/-- Precomposition with the cotangent differential. -/
def homDifferential {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] :
    ((Generators.naive (I := J)).toExtension.CotangentSpace →ₛₗ[φ.toRingHom] N) →ₗ[A]
      relationHom J φ N where
  toFun g := g.comp (Generators.naive (I := J)).toExtension.cotangentComplex
  map_add' := sorry
  map_smul' := sorry

/-- Precomposition with `J/J² ⟶ ⊕ R d x_i` on Hom-spaces. -/
def generatorToRelation {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : Type u) [AddCommGroup N] [Module A N] :
    generatorHom J φ N →ₗ[A] relationHom J φ N where
  toFun g :=
    g.comp
      ((Generators.naive (I := J)).cotangentSpaceBasis.repr.toLinearMap ∘ₗ
        (Generators.naive (I := J)).toExtension.cotangentComplex)
  map_add' := sorry
  map_smul' := sorry

/-- The Hom-coker value of a coefficient module along `φ`. -/
def functorObj {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : ModuleCat A) : ModuleCat A :=
  ModuleCat.of A (relationHom J φ N ⧸ LinearMap.range (homDifferential J φ N))

/-- Postcomposition induces change of coefficients on the cotangent Hom cokernel. -/
def coefficientMap {Λ ι A B : Type u} [CommRing Λ] [CommRing A] [CommRing B]
    [Algebra Λ A] [Algebra Λ B] (J : Ideal (MvPolynomial ι Λ))
    (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
    (σ : A →ₐ[Λ] B) (h : ψ = σ.comp φ)
    {N : ModuleCat A} {N' : ModuleCat B} (f : N →ₛₗ[σ.toRingHom] N') :
    functorObj J φ N →ₗ[A]
      (ModuleCat.restrictScalars σ.toRingHom).obj (functorObj J ψ N') :=
  (LinearMap.range (homDifferential J φ N)).liftQ
    { toFun := fun g ↦ Submodule.Quotient.mk
        { toFun := fun x ↦ f (g x)
          map_add' := by intros; simp
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry } sorry

/-- Identity coefficient maps fix cokernel classes. -/
theorem coefficientMap_id {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (N : ModuleCat A) (x : functorObj J φ N) :
    coefficientMap J φ φ (AlgHom.id Λ A) (by ext; rfl) (LinearMap.id : N →ₗ[A] N) x = x :=
  sorry

/-- Changes of coefficients respect composition. -/
theorem coefficientMap_comp {Λ ι A B C : Type u}
    [CommRing Λ] [CommRing A] [CommRing B] [CommRing C]
    [Algebra Λ A] [Algebra Λ B] [Algebra Λ C]
    (J : Ideal (MvPolynomial ι Λ))
    (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
    (χ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] C)
    (σ : A →ₐ[Λ] B) (τ : B →ₐ[Λ] C)
    (hσ : ψ = σ.comp φ) (hτ : χ = τ.comp ψ)
    {N : ModuleCat A} {N' : ModuleCat B} {N'' : ModuleCat C}
    (f : N →ₛₗ[σ.toRingHom] N') (g : N' →ₛₗ[τ.toRingHom] N'')
    (x : functorObj J φ N) :
    coefficientMap J ψ χ τ hτ g (coefficientMap J φ ψ σ hσ f x) =
      coefficientMap J φ χ (τ.comp σ)
        (by rw [hτ, hσ]; rfl) (g.comp f) x :=
  sorry

/-- Postcomposition over a fixed coefficient ring. -/
private def functorMap {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    {N N' : ModuleCat A} (f : N ⟶ N') :
    functorObj J φ N ⟶ functorObj J φ N' :=
  ModuleCat.ofHom (coefficientMap J φ φ (AlgHom.id Λ A) (by ext; rfl) f.hom)

/-- The coefficient-module functor of the cotangent Hom cokernel. -/
def functor {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ModuleCat A ⥤ ModuleCat A where
  obj := functorObj J φ
  map := functorMap J φ
  map_id N := by ext x; exact coefficientMap_id J φ N x
  map_comp f g := by
    ext x
    exact (coefficientMap_comp J φ φ φ (AlgHom.id Λ A) (AlgHom.id Λ A)
      (by ext; rfl) (by ext; rfl) f.hom g.hom x).symm

/-- The cotangent Hom-cokernel functor is coefficient-ring linear. -/
theorem functorModuleLinear {Λ ι A : Type u} [CommRing Λ] [CommRing A] [Algebra Λ A]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    (functor J φ).ModuleLinear A := sorry

/-- The obstruction module `O_x(I)` as the Hom-coker of the presentation complex. -/
public abbrev module {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) : Type u :=
  relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom) ⧸ LinearMap.range (homDifferential J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom))

/-- The source Hom-coker `Hom_R(J/J², I) / Hom_R(R^{⊕ι}, I)`. -/
abbrev homCoker {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) : Type u :=
  relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom) ⧸ LinearMap.range (generatorToRelation J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom))

/-- The comparison from the cotangent Hom-coker to the free-generator Hom-coker. -/
def homCokerMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ →ₗ[A] homCoker π J φ :=
  (LinearMap.range (homDifferential J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom))).liftQ
    (LinearMap.range (generatorToRelation J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom))).mkQ sorry

/-- The natural comparison of cotangent and free-coordinate Hom cokernels is bijective. -/
theorem homCokerMap_bijective {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    Function.Bijective (homCokerMap π J φ) :=
  sorry

/-- The relation map sending the class of `f ∈ J` to `aeval a' f ∈ I`. -/
def relationMap {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((Generators.naive (I := J)).val i)) :
    relationHom J φ (RingHom.SquareZeroExtension.KernelModule π.toRingHom) where
  toFun x :=
    QuotientAddGroup.lift _
      { toFun := fun f : (Generators.naive (I := J)).ker ↦ ⟨aeval a' f.1, sorry⟩
        map_zero' := sorry
        map_add' := sorry } sorry x.val
  map_add' := sorry
  map_smul' := sorry

/-- `relationMap` evaluates a cotangent representative by the chosen lifts. -/
theorem relationMap_apply {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((Generators.naive (I := J)).val i))
    (f : (Generators.naive (I := J)).ker) :
    (relationMap π J φ a' ha' (Cotangent.mk f)).1 = aeval a' f.1 :=
  sorry

/-- The obstruction class of a choice of coordinate lifts. -/
public def ofLifts {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((Generators.naive (I := J)).val i)) :
    module π J φ :=
  Submodule.Quotient.mk (relationMap π J φ a' ha')

/-- Coordinatewise lifts of the images of the presentation generators. -/
private def coordinateLift {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [hπ : π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    ι → A' :=
  fun i ↦ Function.surjInv hπ.surjective (φ ((Generators.naive (I := J)).val i))

/-- `coordinateLift` lifts the images of the presentation generators. -/
private theorem coordinateLift_spec {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) (i : ι) :
    π (coordinateLift π J φ i) = φ ((Generators.naive (I := J)).val i) :=
  Function.surjInv_eq _ _

/-- The obstruction class `o_x(A')`. -/
public def obstruction {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    module π J φ :=
  ofLifts π J φ (coordinateLift π J φ) (coordinateLift_spec π J φ)

/-- The obstruction class agrees with the evaluation of any choice of coordinate lifts. -/
theorem obstruction_eq_ofLifts {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a' : ι → A') (ha' : ∀ i, π (a' i) = φ ((Generators.naive (I := J)).val i)) :
    obstruction π J φ = ofLifts π J φ a' ha' :=
  sorry

/-- The evaluation-of-lifts class is independent of the chosen lifts of the coordinates. -/
theorem independent {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A)
    (a₁ a₂ : ι → A')
    (ha₁ : ∀ i, π (a₁ i) = φ ((Generators.naive (I := J)).val i))
    (ha₂ : ∀ i, π (a₂ i) = φ ((Generators.naive (I := J)).val i)) :
    ofLifts π J φ a₁ ha₁ = ofLifts π J φ a₂ ha₂ :=
  (obstruction_eq_ofLifts π J φ a₁ ha₁).symm.trans
    (obstruction_eq_ofLifts π J φ a₂ ha₂)

/-- The obstruction vanishes if and only if `φ` lifts through `π`. -/
theorem eq_zero_iff_hasLift {Λ ι A' A : Type u} [CommRing Λ] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ)) (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) :
    obstruction π J φ = 0 ↔ AlgHom.HasLift π φ :=
  sorry

/-- Postcomposition on square-zero kernels along a morphism of deformation squares. -/
def kernelMap {Λ A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) :
    RingHom.SquareZeroExtension.KernelModule π.toRingHom →ₛₗ[σ.toRingHom] RingHom.SquareZeroExtension.KernelModule ρ.toRingHom where
  toFun x := ⟨τ x.val, sorry⟩
  map_add' := sorry
  map_smul' := sorry

/-- `kernelMap` is evaluation of the source-ring map on kernel elements. -/
theorem kernelMap_apply {Λ A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) (x : RingHom.SquareZeroExtension.KernelModule π.toRingHom) :
    (kernelMap π ρ τ σ hcomm x).1 = τ x.val :=
  rfl

/-- The induced map of obstruction modules along a morphism of square-zero squares. -/
public def map {Λ ι A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ))
    (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) (hφψ : ψ = σ.comp φ) :
    module π J φ →ₗ[A]
      (ModuleCat.restrictScalars σ.toRingHom).obj
        (ModuleCat.of B (module ρ J ψ)) :=
  coefficientMap J φ ψ σ hφψ
    (N := ModuleCat.of A (RingHom.SquareZeroExtension.KernelModule π.toRingHom))
    (N' := ModuleCat.of B (RingHom.SquareZeroExtension.KernelModule ρ.toRingHom))
    (kernelMap π ρ τ σ hcomm)

/-- Functoriality of the obstruction class along a morphism of square-zero squares. -/
theorem map_obstruction {Λ ι A' A B' B : Type u}
    [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
    [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B]
    (π : A' →ₐ[Λ] A) [π.toRingHom.IsSquareZeroExtension]
    (ρ : B' →ₐ[Λ] B) [ρ.toRingHom.IsSquareZeroExtension]
    (J : Ideal (MvPolynomial ι Λ))
    (φ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] A) (ψ : (MvPolynomial ι Λ ⧸ J) →ₐ[Λ] B)
    (τ : A' →ₐ[Λ] B') (σ : A →ₐ[Λ] B)
    (hcomm : ρ.comp τ = σ.comp π) (hφψ : ψ = σ.comp φ) :
    map π ρ J φ ψ τ σ hcomm hφψ (obstruction π J φ) = obstruction ρ J ψ :=
  sorry

end Algebra.NaiveCotangent.Obstruction
