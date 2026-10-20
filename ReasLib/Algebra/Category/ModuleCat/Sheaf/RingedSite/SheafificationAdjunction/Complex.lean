/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction

/-!
# Fixed-ring module sheafification of cochain complexes

This file lifts the fixed-ring module-sheafification adjunction degreewise to cochain complexes.
It exposes the underlying presheaf complex and the induced linear equivalence on homogeneous
cochains, independently of any particular tensor-product construction.
-/

@[expose] public section

noncomputable section

universe u v w z

open CategoryTheory
open CochainComplex.HomComplex

namespace SheafOfModules.RingedSite.ModuleSheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable (𝒪 : Sheaf J CommRingCat.{w})

/-- Fixed-ring module sheafification preserves addition. -/
noncomputable instance additive : (moduleSheafification 𝒪).Additive := sorry

/-- The underlying module-presheaf complex of a complex of module sheaves. -/
abbrev underlyingComplex
    (K : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) ℤ) :
    CochainComplex (PresheafOfModules.{z} (ringSheaf J 𝒪).obj) ℤ :=
  ((SheafOfModules.forget (ringSheaf J 𝒪)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- Apply the module-sheafification Hom equivalence to every component of a homogeneous
cochain. -/
def cochainForward
    (P : CochainComplex (PresheafOfModules.{z} (ringSheaf J 𝒪).obj) ℤ)
    (X : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) ℤ) {k : ℤ}
    (f : Cochain
      (((moduleSheafification 𝒪).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) X k) :
    Cochain P (underlyingComplex 𝒪 X) k :=
  Cochain.mk fun p q h ↦
    moduleSheafificationHomEquiv 𝒪 (P.X p) (X.X q) (f.v p q h)

/-- Invert the module-sheafification Hom equivalence in every component of a homogeneous
cochain. -/
def cochainBackward
    (P : CochainComplex (PresheafOfModules.{z} (ringSheaf J 𝒪).obj) ℤ)
    (X : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) ℤ) {k : ℤ}
    (f : Cochain P (underlyingComplex 𝒪 X) k) :
    Cochain
      (((moduleSheafification 𝒪).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) X k :=
  Cochain.mk fun p q h ↦
    (moduleSheafificationHomEquiv 𝒪 (P.X p) (X.X q)).symm (f.v p q h)

/-- Homogeneous maps out of a degreewise sheafified complex are linearly equivalent to
homogeneous maps from its underlying presheaf complex. -/
@[stacks 03L6 "cochain Hom equivalence for module sheafification"]
def cochainEquiv
    (P : CochainComplex (PresheafOfModules.{z} (ringSheaf J 𝒪).obj) ℤ)
    (X : CochainComplex (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) ℤ) (k : ℤ) :
    Cochain
        (((moduleSheafification 𝒪).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) X k
      ≃ₗ[ℤ] Cochain P (underlyingComplex 𝒪 X) k where
  toFun := cochainForward 𝒪 P X
  invFun := cochainBackward 𝒪 P X
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

end SheafOfModules.RingedSite.ModuleSheafification
