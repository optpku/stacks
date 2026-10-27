/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.RelativeDiagram
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.KernelComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials

/-!
# Compatible fillings of relative first-order diagrams

A filling is a ringed-space map with the prescribed two faces and kernel map. Relative
derivations act by addition in the square-zero kernel, and differences of fillings descend
to homomorphisms from the sheaf of differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {X2 X'2 S2 S'2 X1 X'1 S1 S'1 : RingedSpace.{u}}
variable {i2 : X2 ⟶ X'2} {f2 : X2 ⟶ S2} {f'2 : X'2 ⟶ S'2} {t2 : S2 ⟶ S'2}
variable {i1 : X1 ⟶ X'1} {f1 : X1 ⟶ S1} {f'1 : X'1 ⟶ S'1} {t1 : S1 ⟶ S'1}
variable {g : X2 ⟶ X1} {s : S2 ⟶ S1} {s' : S'2 ⟶ S'1}
variable [IsFirstOrderThickening i2] [IsFirstOrderThickening t2]
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening t1]

/-- A filling of a relative first-order cube inducing its prescribed kernel map. -/
structure FittingMap (D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s') where
  /-- The filling morphism of ringed spaces `X'₂ ⟶ X'₁`. -/
  hom : X'2 ⟶ X'1
  /-- The top square with `i₂`, `g`, and `i₁` commutes. -/
  comm_top : i2 ≫ hom = g ≫ i1
  /-- The right square with `f'₁`, `f'₂`, and `s'` commutes. -/
  comm_right : hom ≫ f'1 = f'2 ≫ s'
  /-- The filling morphism induces the given `g`-map on kernel ideals. -/
  induces : kernelMapOf i1 g i2 inferInstance hom comm_top = D.ν

namespace FittingMap

variable {D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s'}

/-- Assemble a fitting map from a morphism `X'₂ ⟶ X'₁` and the three compatibility conditions. -/
def of (hom : X'2 ⟶ X'1) (comm_top : i2 ≫ hom = g ≫ i1)
    (comm_right : hom ≫ f'1 = f'2 ≫ s')
    (induces : kernelMapOf i1 g i2 inferInstance hom comm_top = D.ν) :
    FittingMap D where
  hom := hom
  comm_top := comm_top
  comm_right := comm_right
  induces := induces

/-- A fitting map makes the top and right faces commute and induces `ν` on kernels. -/
theorem spec (φ : FittingMap D) :
    i2 ≫ φ.hom = g ≫ i1 ∧ φ.hom ≫ f'1 = f'2 ≫ s' ∧
      kernelMapOf i1 g i2 inferInstance φ.hom φ.comm_top = D.ν := ⟨φ.comm_top, φ.comm_right, φ.induces⟩

/-- A morphism `X'₂ ⟶ X'₁` underlies a fitting map if and only if the two present faces
through it commute and it induces `ν` on kernel ideals. -/
theorem fits_iff (hom : X'2 ⟶ X'1) :
    (∃ φ : FittingMap D, φ.hom = hom) ↔
      ∃ (comm_top : i2 ≫ hom = g ≫ i1),
        hom ≫ f'1 = f'2 ≫ s' ∧
          kernelMapOf i1 g i2 inferInstance hom comm_top = D.ν := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.comm_top, φ.comm_right, φ.induces⟩
  · rintro ⟨htop, hright, hν⟩
    exact ⟨of hom htop hright hν, rfl⟩

/-- Fillings with the same underlying morphism coincide. -/
@[ext] theorem ext {φ φ' : FittingMap D} (h : φ.hom = φ'.hom) : φ = φ' := by
  cases φ
  cases φ'
  cases h
  rfl

end FittingMap


namespace FittingMap

variable {D : RelativeDiagram i2 f2 f'2 t2 i1 f1 f'1 t1 g s s'}

/-- The derivation `α ∘ d[f₁]` with values in `g_* 𝒢₂`. -/
def perturbDerivation (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) :
    derivations f1 ((g _*).obj (idealModule i2)) :=
  (d[f1]).postcomp α.val

/-- Underlying continuous maps of `i₂ ≫ φ` and `g ≫ i₁` agree. -/
def comm_top_base_eq (φ : FittingMap D) :
    i2.hom.base ≫ φ.hom.hom.base = g.hom.base ≫ i1.hom.base :=
  congrArg (fun h : X2 ⟶ X'1 ↦ h.hom.base) φ.comm_top

/-- Open-set identification induced by `i₂ ≫ φ = g ≫ i₁`. -/
def comm_top_preimage (φ : FittingMap D) (U : Opens X'1) :
    (Opens.map g.hom.base).obj ((Opens.map i1.hom.base).obj U) =
      (Opens.map i2.hom.base).obj ((Opens.map φ.hom.hom.base).obj U) :=
  (congrArg (fun f : X2.carrier ⟶ X'1.carrier ↦ (Opens.map f).obj U)
    (comm_top_base_eq φ)).symm

/-- Identification `i₁_* g_* 𝒢₂ ≅ φ_* i₂_* 𝒢₂` along the top face of the cube. -/
def perturbTargetIso (φ : FittingMap D) :
    (i1 _*).obj ((g _*).obj (idealModule i2)) ≅
      (φ.hom _*).obj ((i2 _*).obj (idealModule i2)) :=
  (pushforwardCompIso g i1).symm.app (idealModule i2) ≪≫
    (eqToIso (congrArg (fun h : X2 ⟶ X'1 ↦ (h _*).obj (idealModule i2))
      φ.comm_top)).symm ≪≫
    (pushforwardCompIso i2 φ.hom).app (idealModule i2)

/-- The kernel-ideal section of `i₂` obtained by evaluating `α ∘ d[f₁]` on `i₁^♯` of a
section of `𝒪_{X'₁}`, then transporting along the top face. -/
def perturbKernelSection (α : Ω[f1] ⟶ (g _*).obj (idealModule i2))
    (φ : FittingMap D) (U : (Opens X'1.carrier)ᵒᵖ) (x : X'1.presheaf.obj U) :
    (kernelIdealSheaf i2).val.obj (op ((Opens.map φ.hom.hom.base).obj (unop U))) :=
  (kernelIdealPushforwardIso i2).inv.val.app
      (op ((Opens.map φ.hom.hom.base).obj (unop U)))
    ((perturbTargetIso φ).hom.val.app U
      ((perturbDerivation α).d ((commRingSheafPushforwardMap i1).hom.app U x)))

/-- Square-zero inclusion of the perturbation section into `φ_* 𝒪_{X'₂}`. -/
def perturbContribution (α : Ω[f1] ⟶ (g _*).obj (idealModule i2))
    (φ : FittingMap D) (U : (Opens X'1.carrier)ᵒᵖ) (x : X'1.presheaf.obj U) :
    (φ.hom.hom.base _* X'2.presheaf).obj U :=
  KernelIdeal.ιApp (commRingSheafPushforwardMap i2)
    (op ((Opens.map φ.hom.hom.base).obj (unop U)))
    (perturbKernelSection α φ U x)

/-- Adding the square-zero derivation preserves the ring operations. -/
private theorem perturbRingHom_laws (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D)
    (U : (Opens X'1.carrier)ᵒᵖ) :
    (φ.hom.hom.c.app U 0 + perturbContribution α φ U 0 = 0) ∧
    (φ.hom.hom.c.app U 1 + perturbContribution α φ U 1 = 1) ∧
    (∀ x y, φ.hom.hom.c.app U (x + y) + perturbContribution α φ U (x + y) =
      (φ.hom.hom.c.app U x + perturbContribution α φ U x) +
      (φ.hom.hom.c.app U y + perturbContribution α φ U y)) ∧
    (∀ x y, φ.hom.hom.c.app U (x * y) + perturbContribution α φ U (x * y) =
      (φ.hom.hom.c.app U x + perturbContribution α φ U x) *
      (φ.hom.hom.c.app U y + perturbContribution α φ U y)) := sorry

/-- The component ring homomorphism adds the specified square-zero derivation. -/
@[no_expose] def perturbRingHom (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D)
    (U : (Opens X'1.carrier)ᵒᵖ) :
    X'1.presheaf.obj U →+* (φ.hom.hom.base _* X'2.presheaf).obj U where
  toFun x := φ.hom.hom.c.app U x + perturbContribution α φ U x
  map_zero' := (perturbRingHom_laws α φ U).1
  map_one' := (perturbRingHom_laws α φ U).2.1
  map_add' := (perturbRingHom_laws α φ U).2.2.1
  map_mul' := (perturbRingHom_laws α φ U).2.2.2

/-- The perturbed component maps commute with restriction of sections. -/
private theorem perturbStructureSheaf_naturality (α : Ω[f1] ⟶ (g _*).obj (idealModule i2))
    (φ : FittingMap D) {U V : (Opens X'1.carrier)ᵒᵖ} (i : U ⟶ V) :
    X'1.presheaf.map i ≫ CommRingCat.ofHom (perturbRingHom α φ V) =
      CommRingCat.ofHom (perturbRingHom α φ U) ≫
        (φ.hom.hom.base _* X'2.presheaf).map i := sorry

/-- The structure-sheaf map of `φ`, modified by the square-zero inclusion of
`α ∘ d[f₁]` into `Ker(i₂^♯)`. -/
@[no_expose] def perturbStructureSheaf (α : Ω[f1] ⟶ (g _*).obj (idealModule i2))
    (φ : FittingMap D) :
    X'1.presheaf ⟶ φ.hom.hom.base _* X'2.presheaf where
  app U := CommRingCat.ofHom (perturbRingHom α φ U)
  naturality {U V} i := perturbStructureSheaf_naturality α φ i

/-- The filling morphism of ringed spaces obtained by perturbing `φ` by `α`. The underlying
continuous map is unchanged; the structure-sheaf map is that of `φ`, modified by the derivation
`α ∘ d[f₁]` through the square-zero kernel of `i₂`. -/
def perturbHom (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    X'2 ⟶ X'1 :=
  InducedCategory.homMk
    { base := φ.hom.hom.base
      c := perturbStructureSheaf α φ }

/-- Perturbation preserves both faces and the prescribed kernel map. -/
private theorem perturb_compatibility (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    (i2 ≫ perturbHom α φ = g ≫ i1) ∧
    (perturbHom α φ ≫ f'1 = f'2 ≫ s') ∧
    (∀ w : i2 ≫ perturbHom α φ = g ≫ i1,
      kernelMapOf i1 g i2 inferInstance (perturbHom α φ) w = D.ν) := sorry

/-- The action of `Hom(Ω[f₁], g_* 𝒢₂)` on fitting maps, adding `α ∘ d[f₁]` through the
square-zero kernel of `i₂`. -/
@[no_expose] def perturb (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    FittingMap D :=
  FittingMap.of (perturbHom α φ) (perturb_compatibility α φ).1
    (perturb_compatibility α φ).2.1 ((perturb_compatibility α φ).2.2 _)

/-- `perturb` does not change the underlying continuous map of the filling morphism. -/
theorem perturb_hom (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    (perturb α φ).hom.hom.base = φ.hom.hom.base := by rfl

/-- Two fitting maps have the same underlying continuous map, because both fill the top face
of the cube and `i₂` is a homeomorphism. -/
def hom_base_eq (φ φ' : FittingMap D) :
    φ.hom.hom.base = φ'.hom.hom.base :=
  Iff.mp (cancel_epi i2.hom.base)
    ((comm_top_base_eq φ).trans (comm_top_base_eq φ').symm)

/-- The open of `X'₁` corresponding to an open of `X₁` along the thickening homeomorphism `i₁`. -/
def correspondingOpen (h : X1 ⟶ X'1) [IsFirstOrderThickening h] (V : Opens X1.carrier) :
    Opens X'1.carrier :=
  (Opens.map (thickeningBaseIso h).inv).obj V

/-- Identification `i₁⁻¹` of the corresponding open with the original open of `X₁`. -/
def correspondingOpenIso (h : X1 ⟶ X'1) [IsFirstOrderThickening h] (V : Opens X1.carrier) :=
  (Opens.mapMapIso (thickeningBaseIso h)).counitIso.app V

/-- `φ'^♯` as a structure-sheaf map on the same pushforward as `φ^♯`. -/
def transportedStructureSheaf (φ φ' : FittingMap D) :
    X'1.presheaf ⟶ φ.hom.hom.base _* X'2.presheaf :=
  φ'.hom.hom.c ≫ (TopCat.Presheaf.pushforwardEq (hom_base_eq φ φ').symm X'2.presheaf).hom

/-- Differences of compatible structure-sheaf maps lie in the thickening kernel. -/
private theorem structureSheafDiffSection_mem (φ φ' : FittingMap D)
    (U : (Opens X'1.carrier)ᵒᵖ) (x : X'1.presheaf.obj U) :
    (transportedStructureSheaf φ φ').app U x - φ.hom.hom.c.app U x ∈
      KernelIdeal.sectionIdeal (commRingSheafPushforwardMap i2)
        (op ((Opens.map φ.hom.hom.base).obj U.unop)) := sorry

/-- The difference of two structure-sheaf maps, as a section of `Ker(i₂^♯)`. -/
@[no_expose] def structureSheafDiffSection (φ φ' : FittingMap D)
    (U : (Opens X'1.carrier)ᵒᵖ) (x : X'1.presheaf.obj U) :
    (kernelIdealSheaf i2).val.obj (op ((Opens.map φ.hom.hom.base).obj (unop U))) :=
  (KernelIdeal.sectionsIso (commRingSheafPushforwardMap i2)
      (op ((Opens.map φ.hom.hom.base).obj (unop U)))).inv
    ⟨(transportedStructureSheaf φ φ').app U x - φ.hom.hom.c.app U x,
      structureSheafDiffSection_mem φ φ' U x⟩

/-- The sectionwise difference is additive and commutes with restriction. -/
private theorem structureSheafDiffAddHom_laws (φ φ' : FittingMap D) :
    (∀ U, structureSheafDiffSection φ φ' U 0 = 0) ∧
    (∀ U x y, structureSheafDiffSection φ φ' U (x + y) =
      structureSheafDiffSection φ φ' U x + structureSheafDiffSection φ φ' U y) ∧
    (∀ {U V : (Opens X'1.carrier)ᵒᵖ} (i : U ⟶ V) (x : X'1.presheaf.obj U),
      structureSheafDiffSection φ φ' V (X'1.presheaf.map i x) =
        ((φ.hom _*).obj (kernelIdealSheaf i2)).val.map i
          (structureSheafDiffSection φ φ' U x)) := sorry

/-- The difference of two structure-sheaf maps as an additive sheaf morphism. -/
@[no_expose] def structureSheafDiffAddHom (φ φ' : FittingMap D) :
    (SheafOfModules.toSheaf X'1.ringCatSheaf).obj (SheafOfModules.unit X'1.ringCatSheaf) ⟶
      (SheafOfModules.toSheaf X'1.ringCatSheaf).obj ((φ.hom _*).obj (kernelIdealSheaf i2)) :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun x := structureSheafDiffSection φ φ' U x
          map_zero' := (structureSheafDiffAddHom_laws φ φ').1 U
          map_add' := (structureSheafDiffAddHom_laws φ φ').2.1 U }
      naturality := by
        intro U V i
        ext x
        exact (structureSheafDiffAddHom_laws φ φ').2.2 i x }

/-- The additive difference vanishes on the kernel of the reduction map. -/
private theorem structureSheafDiffFactor_annihilates (φ φ' : FittingMap D) :
    kernel.ι ((SheafOfModules.toSheaf X'1.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom i1))) ≫
        structureSheafDiffAddHom φ φ' = 0 := sorry

/-- Factorization of the additive structure-sheaf difference through the epimorphism `i₁^♯`. -/
@[no_expose] def structureSheafDiffFactor (φ φ' : FittingMap D) :
    (SheafOfModules.toSheaf X'1.ringCatSheaf).obj
        ((i1 _*).obj (SheafOfModules.unit X1.ringCatSheaf)) ⟶
      (SheafOfModules.toSheaf X'1.ringCatSheaf).obj ((φ.hom _*).obj (kernelIdealSheaf i2)) :=
  CategoryTheory.Abelian.epiDesc
    ((SheafOfModules.toSheaf X'1.ringCatSheaf).map
      (SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom i1)))
    (structureSheafDiffAddHom φ φ') (structureSheafDiffFactor_annihilates φ φ')

/-- Transport a section of `𝒪_{X₁}` to the corresponding open of `X'₁` along `i₁`. -/
def correspondingOpenSection (h : X1 ⟶ X'1) [IsFirstOrderThickening h]
    (V : Opens X1.carrier) (b : X1.presheaf.obj (op V)) :=
  X1.presheaf.map (correspondingOpenIso h V).hom.op b

/-- The `𝒪_{X₁}`-valued difference of two fitting maps, obtained by applying the factored
difference of structure-sheaf maps to the section of `i₁_* 𝒪_{X₁}` corresponding to `b`. -/
def differenceSection (φ φ' : FittingMap D) (V : (Opens X1.carrier)ᵒᵖ)
    (b : X1.presheaf.obj V) :
    ((g _*).obj (idealModule i2)).val.obj V :=
  ((g _*).obj (idealModule i2)).val.map (correspondingOpenIso i1 (unop V)).inv.op
    (addToModuleSection
      ((pushforwardAppAddIso i1 ((g _*).obj (idealModule i2))
          (op (correspondingOpen i1 (unop V)))).hom
        ((perturbTargetIso φ).inv.val.app (op (correspondingOpen i1 (unop V)))
          (((φ.hom _*).map (kernelIdealPushforwardIso i2).hom).val.app
            (op (correspondingOpen i1 (unop V)))
            ((structureSheafDiffFactor φ φ').hom.app (op (correspondingOpen i1 (unop V)))
              ((pushforwardAppAddIso i1 (SheafOfModules.unit X1.ringCatSheaf)
                  (op (correspondingOpen i1 (unop V)))).inv
                ((unitAppAddIso
                    (op ((Opens.map i1.hom.base).obj (correspondingOpen i1 (unop V))))).inv
                  ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
                    ((forget₂ CommRingCat.{u} RingCat.{u}).map (𝟙 _))
                    (correspondingOpenSection i1 (unop V) b)))))))))

/-- The descended difference satisfies the derivation laws and commutes with restriction. -/
private theorem differenceDerivation_laws (φ φ' : FittingMap D) :
    (∀ V x y, differenceSection φ φ' V (x + y) =
      differenceSection φ φ' V x + differenceSection φ φ' V y) ∧
    (∀ V x y, differenceSection φ φ' V (x * y) =
      x • differenceSection φ φ' V y + y • differenceSection φ φ' V x) ∧
    (∀ V x, differenceSection φ φ' V
      ((inverseImageStructureSheafHomComm f1).hom.app V x) = 0) ∧
    (∀ {U V : (Opens X1.carrier)ᵒᵖ} (i : U ⟶ V) (x : X1.presheaf.obj U),
      differenceSection φ φ' V (X1.presheaf.map i x) =
        ((g _*).obj (idealModule i2)).val.map i (differenceSection φ φ' U x)) := sorry

/-- The difference of two compatible fillings is a relative derivation. -/
@[no_expose] def differenceDerivation (φ φ' : FittingMap D) :
    derivations f1 ((g _*).obj (idealModule i2)) :=
  PresheafOfModules.Derivation'.mk
    (fun V ↦ ModuleCat.Derivation.mk (fun b ↦ differenceSection φ φ' V b)
      ((differenceDerivation_laws φ φ').1 V)
      ((differenceDerivation_laws φ φ').2.1 V)
      ((differenceDerivation_laws φ φ').2.2.1 V))
    (fun _ _ i x ↦ (differenceDerivation_laws φ φ').2.2.2 i x)

/-- The `Hom(Ω[f₁], g_* 𝒢₂)` measuring the difference of two fitting maps, obtained by
descent of the difference of structure-sheaf maps through `d[f₁]`. -/
def diff (φ φ' : FittingMap D) : Ω[f1] ⟶ (g _*).obj (idealModule i2) :=
  differentialDesc f1 (differenceDerivation φ φ')

/-- `diff` is the unique `Hom(Ω, g_* 𝒢₂)` comparing two fitting maps. -/
theorem diff_spec (φ φ' : FittingMap D) : perturb (diff φ φ') φ = φ' := sorry

/-- The difference from a filling to its perturbation is the acting homomorphism. -/
theorem diff_perturb (α : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    diff φ (perturb α φ) = α := sorry

/-- Perturbing by the zero homomorphism fixes a filling. -/
theorem perturb_zero (φ : FittingMap D) : perturb 0 φ = φ := sorry

/-- Successive perturbations add their homomorphisms. -/
theorem perturb_add (α β : Ω[f1] ⟶ (g _*).obj (idealModule i2)) (φ : FittingMap D) :
    perturb (α + β) φ = perturb α (perturb β φ) := sorry

end FittingMap


end AlgebraicGeometry.RingedSpace.Thickening
