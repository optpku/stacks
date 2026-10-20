/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Derivations on affine global sections

Taking sections on the top open of an affine scheme sends relative derivations of module sheaves
to derivations of their modules of global sections.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.AffineDerivation

variable {R A : CommRingCat.{u}}

/-- Taking sections on the top open of an affine scheme sends a relative sheaf derivation to the
corresponding derivation of the module of global sections. -/
noncomputable def globalSections (φ : R ⟶ A) (ℱ : (Spec A).Modules) :
    SheafOfModules.RelativeDerivation (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) ℱ →
      ((moduleSpecΓFunctor (R := A)).obj ℱ).Derivation φ :=
  fun D ↦ ModuleCat.Derivation.mk
    (fun a ↦ (D.app (op ⊤)).d ((Scheme.ΓSpecIso A).inv a))
    (by
      intro a b
      simp only [PresheafOfModules.Derivation'.app_apply]
      rw [(Scheme.ΓSpecIso A).inv.hom.map_add]
      exact map_add (D.d (X := op ⊤)) _ _)
    (by
      intro a b
      simp only [PresheafOfModules.Derivation'.app_apply]
      change D.d ((Scheme.ΓSpecIso A).inv (a * b)) =
        (Scheme.ΓSpecIso A).inv a • D.d ((Scheme.ΓSpecIso A).inv b) +
          (Scheme.ΓSpecIso A).inv b • D.d ((Scheme.ΓSpecIso A).inv a)
      rw [(Scheme.ΓSpecIso A).inv.hom.map_mul]
      exact D.d_mul ((Scheme.ΓSpecIso A).inv a) ((Scheme.ΓSpecIso A).inv b))
    (by sorry)

/-- The derivation induced on affine global sections evaluates a sheaf derivation on the top
open after identifying the coefficient ring with the global functions on its spectrum. -/
@[simp]
theorem globalSections_apply (φ : R ⟶ A) (ℱ : (Spec A).Modules)
    (D : SheafOfModules.RelativeDerivation (J := Opens.grothendieckTopology (Spec A))
      (RingedSpace.Hom.inverseImageStructureSheafHomComm (Spec.map φ).toShHom) ℱ)
    (a : A) :
    (globalSections φ ℱ D).d a =
      (D.app (op ⊤)).d ((Scheme.ΓSpecIso A).inv a) := rfl

/-- Taking affine global sections is a bijection from relative derivations of a module sheaf to
relative derivations of its module of global sections. -/
theorem globalSections_bijective (φ : R ⟶ A) (ℱ : (Spec A).Modules) :
    Function.Bijective (globalSections φ ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules.AffineDerivation
