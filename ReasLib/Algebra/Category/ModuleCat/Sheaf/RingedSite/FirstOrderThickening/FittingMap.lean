/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening.RelativeDiagram
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials

/-!
# Fitting morphisms of a relative first-order thickening diagram

After identifying underlying topoi, a fitting map is a morphism of ring sheaves
`𝒪'₁ ⟶ 𝒪'₂` filling the omitted edge of a relative first-order thickening diagram,
compatibly with the given `g`-map of kernel ideals.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

set_option backward.privateInPublic true

open scoped SheafOfModules.RingedSite RelativeDerivation

universe u v w

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O1 O1' OB1 OB1' O2 O2' OB2 OB2' : Sheaf J CommRingCat.{w}}
variable {πO1 : O1' ⟶ O1} {πB1 : OB1' ⟶ OB1}
variable {πO2 : O2' ⟶ O2} {πB2 : OB2' ⟶ OB2}
variable [hπO1 : IsFirstOrderThickening πO1] [hπB1 : IsFirstOrderThickening πB1]
variable [hπO2 : IsFirstOrderThickening πO2] [hπB2 : IsFirstOrderThickening πB2]

/-- A ring-sheaf morphism filling a relative square-zero diagram and inducing its prescribed
map on kernel modules. -/
structure FittingMap (D : RelativeDiagram πO1 πB1 πO2 πB2) where
  /-- The filling morphism of ring sheaves `𝒪'₁ ⟶ 𝒪'₂`. -/
  hom : O1' ⟶ O2'
  /-- The filling morphism is compatible with the thickenings `π_{𝒪ⱼ}`. -/
  comm_π : hom ≫ πO2 = πO1 ≫ D.g
  /-- The filling morphism is compatible with the structure maps `f'ⱼ`. -/
  comm_f' : D.t' ≫ D.f2' = D.f1' ≫ hom
  /-- The filling morphism induces the given `g`-map on kernel ideals. -/
  induces : inducedKernelMap πO1 D.g πO2 hom comm_π = D.ν

namespace FittingMap

variable {D : RelativeDiagram πO1 πB1 πO2 πB2}

/-- Assemble a fitting map from a morphism `𝒪'₁ ⟶ 𝒪'₂` and the three compatibility
conditions. -/
def of (hom : O1' ⟶ O2') (comm_π : hom ≫ πO2 = πO1 ≫ D.g)
    (comm_f' : D.t' ≫ D.f2' = D.f1' ≫ hom)
    (induces : inducedKernelMap πO1 D.g πO2 hom comm_π = D.ν) :
    FittingMap D where
  hom := hom
  comm_π := comm_π
  comm_f' := comm_f'
  induces := induces

/-- A fitting map makes the two present faces through it commute and induces `ν` on
kernels. -/
theorem spec (φ : FittingMap D) :
    φ.hom ≫ πO2 = πO1 ≫ D.g ∧ D.t' ≫ D.f2' = D.f1' ≫ φ.hom ∧
      inducedKernelMap πO1 D.g πO2 φ.hom φ.comm_π = D.ν := ⟨φ.comm_π, φ.comm_f', φ.induces⟩

/-- A morphism `𝒪'₁ ⟶ 𝒪'₂` underlies a fitting map if and only if it fits the relative
diagram in the sense of `RelativeDiagram.Fits`. -/
theorem fits_iff (hom : O1' ⟶ O2') :
    (∃ φ : FittingMap D, φ.hom = hom) ↔ RelativeDiagram.Fits D hom := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.comm_π, φ.comm_f', fun _ ↦ φ.induces⟩
  · rintro ⟨hπ, hf, hν⟩
    exact ⟨of hom hπ hf (hν hπ), rfl⟩

private def perturbKernelSection (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (U : Cᵒᵖ) (x : O1'.obj.obj U) :
    (KernelIdeal.sheaf πO2).val.obj U :=
  ((inferInstance : IsFirstOrderThickening πO2).isSquareZero.targetModuleForgetIso
      inferInstance).hom.hom.app U
    (α.val.app U ((relativeDifferential D.f1).d (πO1.hom.app U x)))

private def perturbContribution (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (U : Cᵒᵖ) (x : O1'.obj.obj U) : O2'.obj.obj U :=
  KernelIdeal.ιApp πO2 U (perturbKernelSection α U x)

/-- Adding a kernel-valued derivation to a fitting ring map preserves the ring laws. -/
private theorem perturbRingHom_laws
    (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) (U : Cᵒᵖ) :
    let f := fun x ↦ φ.hom.hom.app U x + perturbContribution α U x
    f 0 = 0 ∧ f 1 = 1 ∧ (∀ x y, f (x + y) = f x + f y) ∧
      (∀ x y, f (x * y) = f x * f y) := sorry

private def perturbRingHom
    (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) (U : Cᵒᵖ) : O1'.obj.obj U →+* O2'.obj.obj U where
  toFun x := φ.hom.hom.app U x + perturbContribution α U x
  map_zero' := (perturbRingHom_laws α φ U).1
  map_one' := (perturbRingHom_laws α φ U).2.1
  map_add' := (perturbRingHom_laws α φ U).2.2.1
  map_mul' := (perturbRingHom_laws α φ U).2.2.2

/-- Perturbed ring homomorphisms commute with restriction maps. -/
private theorem perturbHom_naturality
    (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) {U V : Cᵒᵖ} (i : U ⟶ V) :
    O1'.obj.map i ≫ CommRingCat.ofHom (perturbRingHom α φ V) =
      CommRingCat.ofHom (perturbRingHom α φ U) ≫ O2'.obj.map i := sorry

private def perturbHom
    (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) : O1' ⟶ O2' :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (perturbRingHom α φ U)
      naturality _ _ i := perturbHom_naturality α φ i }

/-- Perturbation preserves the two fitting faces and the prescribed kernel map. -/
private theorem perturb_compatibility
    (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) :
    (perturbHom α φ) ≫ πO2 = πO1 ≫ D.g ∧
      D.t' ≫ D.f2' = D.f1' ≫ perturbHom α φ ∧
      ∀ hπ : perturbHom α φ ≫ πO2 = πO1 ≫ D.g,
        inducedKernelMap πO1 D.g πO2 (perturbHom α φ) hπ = D.ν := sorry

end FittingMap

variable {D : RelativeDiagram πO1 πB1 πO2 πB2}

/-- Add a relative-differential map to a fitting ring map through the square-zero kernel. -/
def perturb (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) : FittingMap D :=
  FittingMap.of (FittingMap.perturbHom α φ)
    (FittingMap.perturb_compatibility α φ).1
    (FittingMap.perturb_compatibility α φ).2.1
    ((FittingMap.perturb_compatibility α φ).2.2 _)

/-- Perturbation preserves the composite with the target projection. -/
theorem perturb_hom (α : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2))
    (φ : FittingMap D) :
    (perturb α φ).hom ≫ πO2 = φ.hom ≫ πO2 :=
  (perturb α φ).comm_π.trans φ.comm_π.symm

/-- Zero perturbation is the identity and successive perturbations add. -/
theorem perturb_laws (φ : FittingMap D)
    (α β : Ω(D.f1) ⟶ (restrictionAlong D.g).obj (ideal πO2)) :
    perturb 0 φ = φ ∧ perturb α (perturb β φ) = perturb (α + β) φ := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
