/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Sections

/-!
# Hilbert functor as Quot of the structure sheaf

A finite-presentation morphism `f : X ⟶ B` of algebraic spaces has Hilbert
functor `Hilb_{X/B}` naturally isomorphic to `Quot_{𝒪_X/X/B}`. Objectwise, a
closed subspace `Z ⊂ X_T` with `Z ⟶ T` of finite presentation, flat, and proper
is sent to the quotient `𝒪_{X_T} ⟶ ι_* 𝒪_Z` given by `Hom.idealSheafMap`,
transported along `Modules.structureModulePullbackIso` so that the source is
`fiberF f 𝒪_X`. The inverse cuts out `Z` from the kernel of the transported map
`𝒪_{X_T} ⟶ Q`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (fiber fiberF)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The pushforward `ι_* 𝒪_Z` in the encoding of `Hom.idealSheafMap`. -/
def toQuotPointModule {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (p : Point f σ) : (fiber f σ).Modules :=
  (SheafOfModules.pushforward
      (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap p.subspace.ι))).obj
    (SheafOfModules.unit ((ringPushforward p.subspace.ι).obj
      (structureSheaf p.subspace.X)))

/-- The quotient map `π^* 𝒪_X ⟶ ι_* 𝒪_Z` obtained by transporting
`Hom.idealSheafMap` along `Modules.structureModulePullbackIso`. -/
def toQuotPointMap {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (p : Point f σ) :
    fiberF f (SheafOfModules.unit (structureSheaf X)) σ ⟶ toQuotPointModule p :=
  (Modules.structureModulePullbackIso (pullback.fst f σ.hom)).inv ≫
    Hom.idealSheafMap p.subspace.ι

/-- The structure-sheaf quotient of a Hilbert point is epimorphic, quasi-coherent,
flat over the test scheme, finitely presented, and has proper support. -/
theorem toQuotPoint_properties {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (p : Point f σ) :
    Epi (toQuotPointMap p) ∧ (toQuotPointModule p).IsQuasicoherent ∧
      Modules.flatOver (toQuotPointModule p) (pullback.snd f σ.hom) ∧
      (toQuotPointModule p).IsFinitePresentation ∧
      Quot.supportProperOver (pullback.snd f σ.hom) (toQuotPointModule p) := sorry

/-- The Quot-point `𝒪_{X_T} ⟶ ι_* 𝒪_Z` associated to a Hilbert point. -/
def toQuotPoint {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (p : Point f σ) :
    Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ :=
  Quot.QuotPoint.ofEpi f (SheafOfModules.unit (structureSheaf X)) σ
    (toQuotPointModule p) (toQuotPointMap p)
    (toQuotPoint_properties p).1 (toQuotPoint_properties p).2.1
    (toQuotPoint_properties p).2.2.1 (toQuotPoint_properties p).2.2.2.1
    (toQuotPoint_properties p).2.2.2.2

/-- The module of `toQuotPoint p` is `ι_* 𝒪_Z` in the encoding of
`Hom.idealSheafMap`. -/
theorem toQuotPoint_module {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (p : Point f σ) :
    (toQuotPoint p).point.module = toQuotPointModule p := sorry

/-- The quotient map of `toQuotPoint p` is `Hom.idealSheafMap` transported along
`Modules.structureModulePullbackIso`. -/
theorem toQuotPoint_map {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (p : Point f σ) :
    (toQuotPoint p).point.map = toQuotPointMap p := sorry

/-- The structure-sheaf quotient `𝒪_{X_T} ⟶ Q` obtained by transporting a
Quot-point of `𝒪_X` along `Modules.structureModulePullbackIso`. -/
def ofQuotPointMap {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    SheafOfModules.unit (structureSheaf (fiber f σ)) ⟶ Q.point.module :=
  (Modules.structureModulePullbackIso (pullback.fst f σ.hom)).hom ≫ Q.point.map

/-- The quasi-coherent ideal `I = Ker(𝒪_{X_T} ⟶ Q)` of a Quot-point of `𝒪_X`. -/
def ofQuotPointKernel {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    IdealSubobject (fiber f σ) :=
  kernelSubobject (ofQuotPointMap Q)

/-- The kernel of a Quot-point of `𝒪_X` is a quasi-coherent ideal sheaf on `X_T`. -/
theorem ofQuotPointKernel_isQuasiCoherent {f : X ⟶ B} {σ : SchemeOver B}
    [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    IsQuasiCoherent (ofQuotPointKernel Q) := sorry

/-- The closed subspace of `X_T` cut out by `Ker(𝒪_{X_T} ⟶ Q)`. -/
def ofQuotPointSubspace {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    ClosedSubspace (fiber f σ) :=
  @ClosedSubspace.ofQuasiCoherentIdeal S (fiber f σ) (ofQuotPointKernel Q)
    (ofQuotPointKernel_isQuasiCoherent Q)

/-- The closed subspace defined by a structure-sheaf Quot-point is finitely
presented, flat, and proper over the test scheme. -/
theorem ofQuotPointSubspace_properties {f : X ⟶ B} {σ : SchemeOver B}
    [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    FinitePresentation ((ofQuotPointSubspace Q).ι ≫ pullback.snd f σ.hom) ∧
      Flat ((ofQuotPointSubspace Q).ι ≫ pullback.snd f σ.hom) ∧
      Proper ((ofQuotPointSubspace Q).ι ≫ pullback.snd f σ.hom) := sorry

/-- The Hilbert point cut out by the kernel of a Quot-point of `𝒪_X`. -/
def ofQuotPoint {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    Point f σ where
  subspace := ofQuotPointSubspace Q
  isFinitePresentation := (ofQuotPointSubspace_properties Q).1
  isFlat := (ofQuotPointSubspace_properties Q).2.1
  isProper := (ofQuotPointSubspace_properties Q).2.2

/-- The closed subspace of `ofQuotPoint Q` is the vanishing locus of
`Ker(𝒪_{X_T} ⟶ Q)`. -/
theorem ofQuotPoint_spec {f : X ⟶ B} {σ : SchemeOver B} [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    (ofQuotPoint Q).subspace.idealSheaf = ofQuotPointKernel Q := sorry

/-- Ideal-sheaf identification of Hilbert points is preserved by `toQuotPoint`. -/
theorem toQuotPoint_rel (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    ∀ (p q : Point f σ),
      (setoid f σ).r p q →
        (Quot.quotSetoid f (SheafOfModules.unit (structureSheaf X)) σ).r
          (toQuotPoint p) (toQuotPoint q) := sorry

/-- Kernel identification of Quot-points of `𝒪_X` is preserved by `ofQuotPoint`. -/
theorem ofQuotPoint_rel (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    ∀ (Q₁ Q₂ : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ),
      (Quot.quotSetoid f (SheafOfModules.unit (structureSheaf X)) σ).r Q₁ Q₂ →
        (setoid f σ).r (ofQuotPoint Q₁) (ofQuotPoint Q₂) := sorry

/-- The two constructions are inverse on Hilbert points up to ideal-sheaf
identification. -/
theorem ofQuotPoint_toQuotPoint {f : X ⟶ B} {σ : SchemeOver B}
    [FinitePresentation f] (p : Point f σ) :
    Rel (ofQuotPoint (toQuotPoint p)) p := sorry

/-- The two constructions are inverse on Quot-points of `𝒪_X` up to kernel
identification. -/
theorem toQuotPoint_ofQuotPoint {f : X ⟶ B} {σ : SchemeOver B}
    [FinitePresentation f]
    (Q : Quot.QuotPoint f (SheafOfModules.unit (structureSheaf X)) σ) :
    Quot.Rel (toQuotPoint (ofQuotPoint Q)).point Q.point := sorry

/-- Send an ideal-sheaf class of Hilbert points to its structure-sheaf quotient class. -/
def toQuot (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    Quotient (setoid f σ) →
      Quotient (Quot.quotSetoid f (SheafOfModules.unit (structureSheaf X)) σ) :=
  _root_.Quotient.map (fun p ↦ toQuotPoint p) (toQuotPoint_rel f σ)

/-- Send a kernel class of structure-sheaf quotients to the closed subspace it defines. -/
def ofQuot (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    Quotient (Quot.quotSetoid f (SheafOfModules.unit (structureSheaf X)) σ) →
      Quotient (setoid f σ) :=
  _root_.Quotient.map (fun Q ↦ ofQuotPoint Q) (ofQuotPoint_rel f σ)

/-- Taking the kernel subspace after the structure-sheaf quotient recovers a Hilbert class. -/
theorem quotEquiv_left_inv (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    Function.LeftInverse (ofQuot f σ) (toQuot f σ) := sorry

/-- Taking the structure-sheaf quotient after the kernel subspace recovers a Quot class. -/
theorem quotEquiv_right_inv (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    Function.RightInverse (ofQuot f σ) (toQuot f σ) := sorry

/-- Objectwise equivalence identifying Hilbert classes with Quot-classes of
`𝒪_X`. -/
def quotEquiv (f : X ⟶ B) [FinitePresentation f] (σ : SchemeOver B) :
    Quotient (setoid f σ) ≃
      Quotient (Quot.quotSetoid f (SheafOfModules.unit (structureSheaf X)) σ) where
  toFun := toQuot f σ
  invFun := ofQuot f σ
  left_inv := quotEquiv_left_inv f σ
  right_inv := quotEquiv_right_inv f σ

/-- The Hilbert–Quot equivalence commutes with pullback along morphisms of test schemes. -/
theorem quotIso_naturality (f : X ⟶ B) [FinitePresentation f]
    {σ τ : (SchemeOver B)ᵒᵖ} (h : σ ⟶ τ) :
    (hilbert f).map h ≫ (quotEquiv f τ.unop).toIso.hom =
      (quotEquiv f σ.unop).toIso.hom ≫
        (Quot.quot f (SheafOfModules.unit (structureSheaf X))).map h := sorry

/-- The natural isomorphism `Hilb_{X/B} ≅ Quot_{𝒪_X/X/B}` of functors
`(Sch/B)ᵒᵖ ⥤ Type (u + 1)`. -/
def quotIso (f : X ⟶ B) [FinitePresentation f] :
    hilbert f ≅ Quot.quot f (SheafOfModules.unit (structureSheaf X)) :=
  NatIso.ofComponents (fun σ ↦ (quotEquiv f σ.unop).toIso) (quotIso_naturality f)

/-- The component of `quotIso` at a test scheme is the objectwise equivalence
`quotEquiv`. -/
theorem quotIso_app (f : X ⟶ B) [FinitePresentation f] (σ : (SchemeOver B)ᵒᵖ) :
    (quotIso f).app σ = (quotEquiv f σ.unop).toIso := sorry

/-- The forward component of `quotIso` is the function of `quotEquiv`. -/
theorem quotIso_hom_app (f : X ⟶ B) [FinitePresentation f]
    (σ : (SchemeOver B)ᵒᵖ) :
    (quotIso f).hom.app σ = (quotEquiv f σ.unop).toIso.hom := sorry

/-- The inverse component of `quotIso` is the inverse function of `quotEquiv`. -/
theorem quotIso_inv_app (f : X ⟶ B) [FinitePresentation f]
    (σ : (SchemeOver B)ᵒᵖ) :
    (quotIso f).inv.app σ = (quotEquiv f σ.unop).toIso.inv := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert

