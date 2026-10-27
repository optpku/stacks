/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange

/-!
# Connections on a commutative ringed site

A connection is linear over the coefficient sheaf and satisfies the Leibniz rule over
the structure sheaf. Its values lie in the sheaf tensor product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {A O : Sheaf J CommRingCat.{max u v}}

/-- Exterior forms normalized to the structure module in degree zero and the given
module in degree one. -/
def form (O : Sheaf J CommRingCat.{max u v})
    (Ω : ringedSiteModuleCategory J O) : ℕ → ringedSiteModuleCategory J O
  | 0 => unitModule J O
  | 1 => Ω
  | n + 2 => ExteriorPower.sheaf O Ω (n + 2)

/-- Normalized forms are canonically the exterior powers of the module. -/
def formIso (Ω : ringedSiteModuleCategory J O) :
    (n : ℕ) → form O Ω n ≅ ExteriorPower.sheaf O Ω n
  | 0 => (ExteriorPower.degreeZeroIso O Ω).symm
  | 1 => ExteriorPower.degreeOneIso O Ω
  | n + 2 => Iso.refl _

/-- Exterior multiplication of normalized form sheaves. -/
def formWedge (Ω : ringedSiteModuleCategory J O) (i j : ℕ) :
    moduleTensor (form O Ω i) (form O Ω j) ⟶ form O Ω (i + j) :=
  moduleTensorMap (formIso Ω i).hom (formIso Ω j).hom ≫
    ExteriorPower.mul O Ω i j ≫ (formIso Ω (i + j)).inv

/-- Exterior multiplication on local sections of normalized form sheaves. -/
def formWedgeApp (Ω : ringedSiteModuleCategory J O) (i j : ℕ) (U : Cᵒᵖ)
    (α : (form O Ω i).val.obj U) (β : (form O Ω j).val.obj U) :
    (form O Ω (i + j)).val.obj U :=
  (formWedge Ω i j).val.app U (tensorSection O U α β)

/-- A connection relative to a derivation into a module sheaf. -/
structure Connection (φ : A ⟶ O) (Ω : ringedSiteModuleCategory J O)
    (D : SheafOfModules.RelativeDerivation φ Ω) (F : ringedSiteModuleCategory J O) where
  /-- The coefficient-linear connection morphism. -/
  hom : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj (moduleTensor F Ω)
  /-- The local Leibniz identity over the structure sheaf. -/
  leibniz (U : Cᵒᵖ) (a : O.obj.obj U) (m : F.val.obj U) :
    hom.val.app U (a • m) =
      ((moduleTensor F Ω).val.obj U).isModule.smul a (hom.val.app U m) + tensorSection O U m (D.d a)

namespace Connection

variable {φ : A ⟶ O} {Ω F : ringedSiteModuleCategory J O}
variable {D : SheafOfModules.RelativeDerivation φ Ω}

/-- Construct a connection from a coefficient-linear morphism and its Leibniz identity. -/
def of (hom : (restrictionAlong φ).obj F ⟶
    (restrictionAlong φ).obj (moduleTensor F Ω))
    (leibniz : ∀ (U : Cᵒᵖ) (a : O.obj.obj U) (m : F.val.obj U),
      hom.val.app U (a • m) =
        ((moduleTensor F Ω).val.obj U).isModule.smul a (hom.val.app U m) + tensorSection O U m (D.d a)) :
    Connection φ Ω D F := ⟨hom, leibniz⟩

/-- Evaluate a connection on a local section. -/
def «apply» (conn : Connection φ Ω D F) (U : Cᵒᵖ) (m : F.val.obj U) :
    (moduleTensor F Ω).val.obj U := conn.hom.val.app U m

end Connection

/-- An exterior calculus consists of coefficient-linear differentials on exterior form
sheaves extending a derivation, satisfying the graded Leibniz rule and square-zero law. -/
structure ExteriorCalculus (φ : A ⟶ O) (Ω : ringedSiteModuleCategory J O)
    (D : SheafOfModules.RelativeDerivation φ Ω) where
  /-- The degree-raising differential, linear over the coefficients. -/
  d (n : ℕ) : (restrictionAlong φ).obj (form O Ω n) ⟶
    (restrictionAlong φ).obj (form O Ω (n + 1))
  /-- The degree-zero differential is the specified derivation. -/
  d_zero (U : Cᵒᵖ) (a : O.obj.obj U) : (d 0).val.app U a = D.d a
  /-- The coefficient Leibniz identity. -/
  d_smul (n : ℕ) (U : Cᵒᵖ) (a : O.obj.obj U) (ω : (form O Ω n).val.obj U) :
    (d n).val.app U (a • ω) =
      ((form O Ω (n + 1)).val.obj U).isModule.smul a ((d n).val.app U ω) +
      (eqToHom (congrArg (form O Ω) (Nat.add_comm 1 n))).val.app U
        (formWedgeApp Ω 1 n U (D.d a) ω)
  /-- The differential is a graded derivation for exterior multiplication. -/
  d_wedge (i j : ℕ) (U : Cᵒᵖ)
      (α : (form O Ω i).val.obj U) (β : (form O Ω j).val.obj U) :
    (d (i + j)).val.app U (formWedgeApp Ω i j U α β) =
      (eqToHom (congrArg (form O Ω) (by omega : i + 1 + j = i + j + 1))).val.app U
        (formWedgeApp Ω (i + 1) j U ((d i).val.app U α) β) +
      (-1 : ℤ) ^ i •
        (eqToHom (congrArg (form O Ω) (by omega : i + (j + 1) = i + j + 1))).val.app U
          (formWedgeApp Ω i (j + 1) U α ((d j).val.app U β))
  /-- Consecutive differentials compose to zero. -/
  d_sq (n : ℕ) : d n ≫ d (n + 1) = 0

namespace ExteriorCalculus

variable {φ : A ⟶ O} {Ω : ringedSiteModuleCategory J O}
variable {D : SheafOfModules.RelativeDerivation φ Ω}

/-- Evaluate an exterior-calculus differential on a local form. -/
def «apply» (E : ExteriorCalculus φ Ω D) (n : ℕ) (U : Cᵒᵖ)
    (ω : (form O Ω n).val.obj U) : (form O Ω (n + 1)).val.obj U :=
  (E.d n).val.app U ω

end ExteriorCalculus

namespace Connection

variable {φ : A ⟶ O} {Ω F : ringedSiteModuleCategory J O}
variable {D : SheafOfModules.RelativeDerivation φ Ω}

/-- Exterior multiplication on the form factor of a module-valued one-form. -/
def wedgeHom (n : ℕ) :
    moduleTensor (moduleTensor F Ω) (form O Ω n) ⟶
      moduleTensor F (form O Ω (n + 1)) :=
  (α_ F Ω (form O Ω n)).hom ≫
    moduleTensorMap (𝟙 F)
      (formWedge Ω 1 n ≫
        eqToHom (congrArg (form O Ω) (Nat.add_comm 1 n)))

/-- The additive balanced pairing defining the extension of a connection to forms. -/
def differentialPairing (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D)
    (n : ℕ) (U : Cᵒᵖ) (m : F.val.obj U) (ω : (form O Ω n).val.obj U) :
    (moduleTensor F (form O Ω (n + 1))).val.obj U :=
  (wedgeHom n).val.app U (tensorSection O U (conn.apply U m) ω) +
    tensorSection O U m (E.apply n U ω)

/-- The extension pairing is additive, balanced over the structure sheaf, coefficient-linear,
and compatible with restriction. -/
theorem differentialPairing_laws (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (n : ℕ) :
    (∀ (U : Cᵒᵖ) (m m' : F.val.obj U) (ω : (form O Ω n).val.obj U),
      differentialPairing conn E n U (m + m') ω =
        differentialPairing conn E n U m ω + differentialPairing conn E n U m' ω) ∧
    (∀ (U : Cᵒᵖ) (m : F.val.obj U) (ω ω' : (form O Ω n).val.obj U),
      differentialPairing conn E n U m (ω + ω') =
        differentialPairing conn E n U m ω + differentialPairing conn E n U m ω') ∧
    (∀ (U : Cᵒᵖ) (a : O.obj.obj U) (m : F.val.obj U) (ω : (form O Ω n).val.obj U),
      differentialPairing conn E n U (a • m) ω = differentialPairing conn E n U m (a • ω)) ∧
    (∀ (U : Cᵒᵖ) (a : A.obj.obj U) (m : F.val.obj U) (ω : (form O Ω n).val.obj U),
      differentialPairing conn E n U ((φ.hom.app U a) • m) ω =
        (φ.hom.app U a) • differentialPairing conn E n U m ω) ∧
    (∀ {U V : Cᵒᵖ} (ρ : U ⟶ V) (m : F.val.obj U) (ω : (form O Ω n).val.obj U),
      (moduleTensor F (form O Ω (n + 1))).val.map ρ
          (differentialPairing conn E n U m ω) =
        differentialPairing conn E n V (F.val.map ρ m) ((form O Ω n).val.map ρ ω)) := sorry

set_option backward.privateInPublic true in
private def pairingAdd (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D)
    (n : ℕ) (U : Cᵒᵖ) :
    F.val.obj U →+ (form O Ω n).val.obj U →+
      (moduleTensor F (form O Ω (n + 1))).val.obj U := by
  have hl := differentialPairing_laws conn E n
  refine
    { toFun := fun m ↦
        { toFun := differentialPairing conn E n U m
          map_zero' := ?_
          map_add' := hl.2.1 U m }
      map_zero' := ?_
      map_add' := ?_ }
  · have h := hl.2.1 U m 0 0
    exact (add_left_cancel (a := differentialPairing conn E n U m 0)
      (by simpa only [add_zero] using h)).symm
  · ext ω
    change differentialPairing conn E n U 0 ω = 0
    have h := hl.1 U 0 0 ω
    exact (add_left_cancel (a := differentialPairing conn E n U 0 ω)
      (by simpa only [add_zero] using h)).symm
  · intro m m'
    ext ω
    exact hl.1 U m m' ω

set_option backward.privateInPublic true in
private def pairingLift (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D)
    (n : ℕ) (U : Cᵒᵖ) :=
  TensorProduct.liftAddHom (pairingAdd conn E n U)
    ((differentialPairing_laws conn E n).2.2.1 U)

set_option backward.privateInPublic true in
private theorem pairingLift_smul (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (n : ℕ) (U : Cᵒᵖ)
    (a : A.obj.obj U)
    (t : F.val.obj U ⊗[O.obj.obj U] (form O Ω n).val.obj U) :
    pairingLift conn E n U ((φ.hom.app U a) • t) =
      (φ.hom.app U a) • pairingLift conn E n U t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul m ω =>
    rw [TensorProduct.smul_tmul']
    change differentialPairing conn E n U ((φ.hom.app U a) • m) ω =
      (φ.hom.app U a) • differentialPairing conn E n U m ω
    exact (differentialPairing_laws conn E n).2.2.2.1 U a m ω
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

set_option backward.privateInPublic true in
private def differentialPresheaf (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (n : ℕ) :
    (PresheafOfModules.restrictScalars (ringSheafMap φ).hom).obj
        (PresheafOfModules.Monoidal.tensorObj F.val (form O Ω n).val) ⟶
      ((restrictionAlong φ).obj (moduleTensor F (form O Ω (n + 1)))).val where
  app U := (ModuleCat.homEquiv
    (M := ((PresheafOfModules.restrictScalars (ringSheafMap φ).hom).obj
      (PresheafOfModules.Monoidal.tensorObj F.val (form O Ω n).val)).obj U)
    (N := ((restrictionAlong φ).obj (moduleTensor F (form O Ω (n + 1)))).val.obj U)).symm
    { toFun := pairingLift conn E n U
      map_add' := map_add _
      map_smul' := pairingLift_smul conn E n U }
  naturality := by
    intro U V ρ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change pairingLift conn E n V
        (((PresheafOfModules.Monoidal.tensorObj F.val (form O Ω n).val).map ρ).hom t) =
      ((moduleTensor F (form O Ω (n + 1))).val.map ρ).hom (pairingLift conn E n U t)
    induction t using TensorProduct.induction_on with
    | zero =>
      erw [((PresheafOfModules.Monoidal.tensorObj F.val (form O Ω n).val).map ρ).hom.map_zero,
        (pairingLift conn E n V).map_zero, (pairingLift conn E n U).map_zero,
        ((moduleTensor F (form O Ω (n + 1))).val.map ρ).hom.map_zero]
      rfl
    | tmul m ω =>
      exact ((differentialPairing_laws conn E n).2.2.2.2 ρ m ω).symm
    | add x y hx hy =>
      erw [((PresheafOfModules.Monoidal.tensorObj F.val (form O Ω n).val).map ρ).hom.map_add,
        (pairingLift conn E n V).map_add, (pairingLift conn E n U).map_add,
        ((moduleTensor F (form O Ω (n + 1))).val.map ρ).hom.map_add, hx, hy]
      rfl

-- Visibility justification: the exposed construction uses private tensor-descent operations
-- whose names remain implementation details rather than public mathematical declarations.
set_option backward.privateInPublic true in
/-- The extended differential on module-valued forms, obtained by balanced tensor descent
and sheafification over the coefficient sheaf. -/
def differential (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D) (n : ℕ) :
    (restrictionAlong φ).obj (moduleTensor F (form O Ω n)) ⟶
      (restrictionAlong φ).obj (moduleTensor F (form O Ω (n + 1))) :=
  (restrictionAlong φ).map (ModuleSheafification.tensorObjIso O F (form O Ω n)).hom ≫
    (ModuleSheafification.restrictionIso φ).inv.app _ ≫
    (moduleSheafificationHomEquiv A _ _).symm (differentialPresheaf conn E n)

/-- The extended differential satisfies the connection formula on pure tensor sections. -/
theorem differential_tmul (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D)
    (n : ℕ) (U : Cᵒᵖ) (m : F.val.obj U) (ω : (form O Ω n).val.obj U) :
    (differential conn E n).val.app U (tensorSection O U m ω) =
      differentialPairing conn E n U m ω := sorry

/-- A connection is integrable if its actual curvature vanishes. -/
def IsIntegrable (conn : Connection φ Ω D F) (E : ExteriorCalculus φ Ω D) : Prop :=
  conn.hom ≫ differential conn E 1 = 0

/-- Integrability makes all consecutive extended differentials compose to zero. -/
theorem squaresToZero_of_isIntegrable (conn : Connection φ Ω D F)
    (E : ExteriorCalculus φ Ω D) (h : IsIntegrable conn E) (n : ℕ) :
    differential conn E n ≫ differential conn E (n + 1) = 0 := sorry

end Connection

end SheafOfModules.RingedSite
