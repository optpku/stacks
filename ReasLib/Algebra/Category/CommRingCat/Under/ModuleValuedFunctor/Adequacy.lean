/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

variable (A : Type u) [CommRing A]
variable {𝓕 : Type v} [Category.{w} 𝓕] [HasZeroMorphisms 𝓕] [HasKernels 𝓕]

/-- An object of a category with kernels has an `A`-module kernel presentation along
an explicitly specified functor from `A`-modules. -/
def Adequate (underline : ModuleCat.{u} A ⥤ 𝓕) (F : 𝓕) : Prop :=
  ∃ (M N : ModuleCat.{u} A) (f : M ⟶ N),
    Nonempty (F ≅ kernel (underline.map f))

/-- The kernel-presentation characterization of `Adequate`. -/
theorem adequate_iff (underline : ModuleCat.{u} A ⥤ 𝓕) (F : 𝓕) :
    Adequate A underline F ↔
      ∃ (M N : ModuleCat.{u} A) (f : M ⟶ N),
        Nonempty (F ≅ kernel (underline.map f)) := sorry

/-- An object has a finite-free `A`-module kernel presentation along an explicitly
specified functor from `A`-modules. -/
def LinearlyAdequate (underline : ModuleCat.{u} A ⥤ 𝓕) (F : 𝓕) : Prop :=
  ∃ (n m : ℕ)
    (f : ModuleCat.of A (Fin n → A) ⟶ ModuleCat.of A (Fin m → A)),
    Nonempty (F ≅ kernel (underline.map f))

/-- The finite-free kernel-presentation characterization of `LinearlyAdequate`. -/
theorem linearlyAdequate_iff (underline : ModuleCat.{u} A ⥤ 𝓕) (F : 𝓕) :
    LinearlyAdequate A underline F ↔
      ∃ (n m : ℕ)
        (f : ModuleCat.of A (Fin n → A) ⟶ ModuleCat.of A (Fin m → A)),
        Nonempty (F ≅ kernel (underline.map f)) := sorry

/-- Finite-free kernel presentations are kernel presentations. -/
theorem LinearlyAdequate.adequate {underline : ModuleCat.{u} A ⥤ 𝓕} {F : 𝓕}
    (hF : LinearlyAdequate A underline F) : Adequate A underline F := sorry

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}
variable [Category (ModuleValuedFunctor.{u, v} A)]
variable [HasZeroMorphisms (ModuleValuedFunctor.{u, v} A)]
variable [HasKernels (ModuleValuedFunctor.{u, v} A)]

/-- A module-valued functor has an `A`-module kernel presentation along a specified
functor into module-valued functors. -/
def Adequate (tensorExtension : ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, v} A)
    (F : ModuleValuedFunctor.{u, v} A) : Prop :=
  _root_.Adequate A tensorExtension F

/-- The kernel-presentation characterization of module-valued-functor adequacy. -/
theorem adequate_iff
    (tensorExtension : ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, v} A)
    (F : ModuleValuedFunctor.{u, v} A) :
    Adequate tensorExtension F ↔
      ∃ (M N : ModuleCat.{u} A) (f : M ⟶ N),
        Nonempty (F ≅ kernel (tensorExtension.map f)) := sorry

/-- A module-valued functor has a finite-free `A`-module kernel presentation along a
specified functor into module-valued functors. -/
def LinearlyAdequate (tensorExtension : ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, v} A)
    (F : ModuleValuedFunctor.{u, v} A) : Prop :=
  _root_.LinearlyAdequate A tensorExtension F

/-- The finite-free kernel-presentation characterization of linear adequacy for
module-valued functors. -/
theorem linearlyAdequate_iff
    (tensorExtension : ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, v} A)
    (F : ModuleValuedFunctor.{u, v} A) :
    LinearlyAdequate tensorExtension F ↔
      ∃ (n m : ℕ)
        (f : ModuleCat.of A (Fin n → A) ⟶ ModuleCat.of A (Fin m → A)),
        Nonempty (F ≅ kernel (tensorExtension.map f)) := sorry

/-- Every linearly adequate module-valued functor is adequate. -/
theorem LinearlyAdequate.adequate
    {tensorExtension : ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, v} A}
    {F : ModuleValuedFunctor.{u, v} A}
    (hF : LinearlyAdequate tensorExtension F) :
    Adequate tensorExtension F := sorry

/-- Adequacy with respect to the canonical tensor-extension functor. -/
def TensorAdequate (F : bundled.{u, u} A) : Prop :=
  @_root_.Adequate A inferInstance (bundled.{u, u} A) inferInstance
    (bundledHasZeroMorphisms.{u, u} A) (bundledHasKernels.{u, u} A)
    (tensorExtensionFunctor A) F

/-- Linear adequacy with respect to the canonical tensor-extension functor. -/
def TensorLinearlyAdequate (F : bundled.{u, u} A) : Prop :=
  @_root_.LinearlyAdequate A inferInstance (bundled.{u, u} A) inferInstance
    (bundledHasZeroMorphisms.{u, u} A) (bundledHasKernels.{u, u} A)
    (tensorExtensionFunctor A) F

end ModuleValuedFunctor
