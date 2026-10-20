/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange

/-!
# De Rham complexes on a ringed site

Relative differential forms for `φ : O₁ ⟶ O₂` are obtained by sheafifying their explicit
sectionwise presentation as `O₂`-modules.  Restricting scalars along `φ` gives the terms of the
de Rham complex over `O₁`.  The differential descends through the general compatibility of module
sheafification with restriction of scalars.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape

universe u v

namespace SheafOfModules.RingedSite.DeRham

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- The sheaf of relative differential `p`-forms, retaining its natural `O₂`-module structure. -/
@[stacks 0FKM]
noncomputable def form (φ : O₁ ⟶ O₂) (p : ℕ) : ringedSiteModuleCategory J O₂ :=
  (moduleSheafification O₂).obj (PresheafOfModules.DeRham.form φ.hom p)

/-- Restriction from `O₂`-module sheaves to `O₁`-module sheaves along `φ`. -/
@[stacks 0FKM "restriction along a morphism of commutative-ring sheaves"]
abbrev restriction (φ : O₁ ⟶ O₂) := restrictionAlong φ

/-- The scalar-restricted degree-`p` term of the relative de Rham complex. -/
@[stacks 0FKM]
noncomputable def term (φ : O₁ ⟶ O₂) (p : ℕ) : ringedSiteModuleCategory J O₁ :=
  (restriction φ).obj (form φ p)

/-- The adjunction unit from the presheaf relative de Rham term to the identity-restricted
presheaf underlying its sheaf-level counterpart. -/
@[stacks 0FKM "term sheafification unit"]
noncomputable def termUnit (φ : O₁ ⟶ O₂) (p : ℕ) :
    PresheafOfModules.DeRham.term φ.hom p ⟶
      (moduleSheafificationRightAdjoint O₁).obj (term φ p) :=
  (moduleSheafificationAdjunction O₁).homEquiv _ _
    (ModuleSheafification.restrictionComponentIso φ
      (PresheafOfModules.DeRham.form φ.hom p)).hom

/-- A basic relative form, mapped into the target-ring module sheaf by the sheafification unit. -/
@[stacks 0FKN "basic sheafified form"]
def basicForm (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ)
    (b₀ : O₂.obj.obj X) (bs : Fin p → O₂.obj.obj X) : (form φ p).val.obj X :=
  ((moduleSheafificationUnit O₂).app
      (PresheafOfModules.DeRham.form φ.hom p)).app X
    (PresheafOfModules.DeRham.basic φ.hom p X b₀ bs)

/-- A basic relative form viewed in the scalar-restricted de Rham term. -/
@[stacks 0FKN "basic form"]
def basic (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ)
    (b₀ : O₂.obj.obj X) (bs : Fin p → O₂.obj.obj X) : (term φ p).val.obj X :=
  basicForm φ p X b₀ bs

/-- The sheafified degree-raising differential between scalar-restricted form sheaves. -/
@[stacks 0FKM]
noncomputable def d (φ : O₁ ⟶ O₂) (p : ℕ) : term φ p ⟶ term φ (p + 1) :=
  ModuleSheafification.mapAfterRestriction φ
    (PresheafOfModules.DeRham.d φ.hom p)

/-- Equation 17.30.1.1 (0FKN): the sheafified differential sends
`b₀ db₁ ∧ ... ∧ dbₚ` to `db₀ ∧ db₁ ∧ ... ∧ dbₚ`. -/
@[stacks 0FKN]
theorem d_basic (φ : O₁ ⟶ O₂) (p : ℕ) (X : Cᵒᵖ)
    (b₀ : O₂.obj.obj X) (bs : Fin p → O₂.obj.obj X) :
    (d φ p).val.app X (basic φ p X b₀ bs) =
      basic φ (p + 1) X 1 (Fin.cons b₀ bs) := sorry

/-- Consecutive sheafified de Rham differentials compose to zero. -/
@[stacks 0FKM "differential squares to zero"]
theorem d_sq (φ : O₁ ⟶ O₂) (p : ℕ) :
    d φ p ≫ d φ (p + 1) = 0 := sorry

/-- Definition 17.30.1 (0FKM): the relative de Rham complex of a morphism of commutative ring
sheaves, as a cochain complex of modules over the source ring sheaf. -/
@[stacks 0FKM]
noncomputable def complex (φ : O₁ ⟶ O₂) :
    CochainComplex (ringedSiteModuleCategory J O₁) ℕ :=
  CochainComplex.of (term φ) (d φ) (d_sq φ)

/-- The degree-`p` term of the ringed-site de Rham complex is the restricted form sheaf. -/
@[stacks 0FKM "term component"]
theorem complex_X (φ : O₁ ⟶ O₂) (p : ℕ) :
    (complex φ).X p = term φ p := sorry

/-- The consecutive-degree map of the ringed-site de Rham complex is `d φ p`. -/
@[stacks 0FKM "differential component"]
theorem complex_d (φ : O₁ ⟶ O₂) (p : ℕ) :
    (complex φ).d p (p + 1) = d φ p := sorry

end SheafOfModules.RingedSite.DeRham

namespace SheafOfModules.RingedSite

/-- The relative de Rham complex of a morphism of commutative ring sheaves. -/
scoped[SheafOfModules.RingedSite] notation:max "Ωᵈᴿ(" φ ")" => DeRham.complex φ

/-- The relative differential `p`-form sheaf with its target-ring module structure. -/
scoped[SheafOfModules.RingedSite] notation:max "Ωᵈᴿ[" p "](" φ ")" => DeRham.form φ p

end SheafOfModules.RingedSite
