module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.CommRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingInverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Realization of square-zero algebras by first-order thickenings

A locally surjective square-zero extension of the small étale structure sheaf with
quasi-coherent kernel is realized by a first-order thickening over the specified base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension

variable {S : Scheme.{u}}

/-- The `𝒪_B`-algebra structure map `sX⁻¹ 𝒪_B ⟶ i⁻¹ 𝒪_{X'}` of a thickening over `B`,
as sheaves of commutative rings on `X_étale`. -/
def algebraMap {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (h : i ≫ sX' = sX) :
    commInverseImageStructureSheaf sX ⟶ commInverseImageStructureSheaf i :=
  (commInverseImageCongr h.symm).hom ≫
    (commSheafInverseImageCompIso i sX' (commStructureSheaf B)).inv ≫
    commSheafInverseImageMap i (commInverseImageStructureSheafMap sX')

/-- `algebraMap` is the transport of `i⁻¹((sX')^♯)` along `sX⁻¹ ≅ i⁻¹ sX'⁻¹`. -/
theorem algebraMap_eq {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (h : i ≫ sX' = sX) :
    algebraMap i sX sX' h =
      (commInverseImageCongr h.symm).hom ≫
        (commSheafInverseImageCompIso i sX' (commStructureSheaf B)).inv ≫
        commSheafInverseImageMap i (commInverseImageStructureSheafMap sX') :=
  rfl

/-- The square-zero kernel of `π : A ⟶ 𝒪_X`, with its canonical module structure over `𝒪_X`. -/
abbrev kernelModule {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :
    RingedSite.ModuleCat.{u} (commRingedSite X) :=
  @KernelIdeal.IsSquareZero.targetModule.{u + 1, u, u}
    (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
    _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π)

/-- `kernelModule π hπ` is the target module of the square-zero kernel of `π`. -/
theorem kernelModule_eq {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :
    kernelModule π hπ =
      @KernelIdeal.IsSquareZero.targetModule.{u + 1, u, u}
        (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
        _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π) :=
  rfl

/-- The underlying additive sheaf of `kernelModule π hπ` is the kernel ideal sheaf of `π`. -/
def kernelModuleForgetIso {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :=
  @KernelIdeal.IsSquareZero.targetModuleForgetIso.{u + 1, u, u}
    (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
    _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π)

/-- `kernelModuleForgetIso` is `targetModuleForgetIso` of the square-zero kernel. -/
theorem kernelModuleForgetIso_eq {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :
    kernelModuleForgetIso π hπ =
      @KernelIdeal.IsSquareZero.targetModuleForgetIso.{u + 1, u, u}
        (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
        _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π) :=
  rfl

/-- A first-order thickening over `B` realizing a square-zero algebra `A` on `X_étale`. -/
structure IsRealization {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A) : Prop where
  /-- The morphism `i` is a first-order thickening. -/
  isFirstOrder : IsFirstOrderThickening i
  /-- The thickening lies over `B` via `s'`. -/
  overBase : i ≫ s' = f
  /-- The comparison `φ : i⁻¹𝒪_{X'} ⟶ A` is an isomorphism. -/
  isIso : IsIso φ
  /-- The isomorphism is compatible with the surjections to `𝒪_X`. -/
  compatibleSurjection : φ ≫ π = commInverseImageStructureSheafMap i
  /-- The isomorphism is a morphism of `f⁻¹𝒪_B`-algebras. -/
  compatibleAlgebra : α = algebraMap i f s' overBase ≫ φ

/-- Assemble a realization from a first-order thickening over `B` and a compatible algebra
isomorphism. -/
def IsRealization.of {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A)
    (h_first : IsFirstOrderThickening i) (h_over : i ≫ s' = f) (h_iso : IsIso φ)
    (h_surj : φ ≫ π = commInverseImageStructureSheafMap i)
    (h_alg : α = algebraMap i f s' h_over ≫ φ) :
    IsRealization f A π hπ α hα i s' φ where
  isFirstOrder := h_first
  overBase := h_over
  isIso := h_iso
  compatibleSurjection := h_surj
  compatibleAlgebra := h_alg

/-- Being a realization unpacks as a first-order thickening over `B` together with a
compatible algebra isomorphism. -/
theorem isRealization_iff {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A) :
    IsRealization f A π hπ α hα i s' φ ↔
      IsFirstOrderThickening i ∧
        ∃ h_over : i ≫ s' = f,
          IsIso φ ∧ φ ≫ π = commInverseImageStructureSheafMap i ∧
            α = algebraMap i f s' h_over ≫ φ :=
  sorry

/-- Given a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` and a locally
surjective square-zero extension
`π : A ⟶ 𝒪_X` of `f⁻¹𝒪_B`-algebras on `X_étale` whose kernel is quasi-coherent as
an `𝒪_X`-module, there exists a first-order thickening `i : X ⟶ X'` over `B` and
an isomorphism `i⁻¹𝒪_{X'} ⟶ A` of `f⁻¹𝒪_B`-algebras compatible with the
surjections to `𝒪_X`. -/
theorem exists_firstOrderThickening {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) [(kernelModule π hπ).IsQuasicoherent]
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f) :
    ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (s' : X' ⟶ B)
      (φ : commInverseImageStructureSheaf i ⟶ A),
      IsRealization f A π hπ α hα i s' φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
