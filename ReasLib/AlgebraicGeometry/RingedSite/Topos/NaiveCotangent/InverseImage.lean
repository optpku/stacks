/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.ModuleObstruction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Functoriality
public import ReasLib.CategoryTheory.Sites.Topos.InternalCommRing
public import Mathlib.Algebra.Category.Ring.Colimits

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open RingedSite.ToposHom.Thickening
open SheafOfModules.RingedSite
noncomputable section
set_option backward.privateInPublic true
universe w
namespace RingedSite.ToposHom.NaiveCotangent

section InverseImage

namespace InverseImage

open CategoryTheory.Sheaf CategoryTheory.Sheaf.InternalRing CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.MorphismOfTopoiIn

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC.HasSheafCompose (forget RingCat.{w})]
variable [JD.HasSheafCompose (forget RingCat.{w})]
variable [JC.HasSheafCompose (forget CommRingCat.{w})]
variable [JD.HasSheafCompose (forget CommRingCat.{w})]
variable [HasWeakSheafify JC CommRingCat.{w}]
variable [HasWeakSheafify JD CommRingCat.{w}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{w}]
variable (f : MorphismOfTopoiIn.{uC, uD, vC, vD, w} JC JD)
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The free algebra functor is left adjoint to its underlying sheaf functor. -/
private def freeForgetAdjunction {E : Type*} [Category* E]
    {K : GrothendieckTopology E} [HasWeakSheafify K CommRingCat.{w}]
    [K.HasSheafCompose (forget CommRingCat.{w})]
    [HasColimitsOfShape (Discrete WalkingPair) (Sheaf K CommRingCat.{w})]
    (A : Sheaf K CommRingCat.{w}) :
    Sheaf.composeAndSheafify K CommRingCat.free ⋙ Under.costar A ⊣
      Under.forget A ⋙ sheafCompose K (forget CommRingCat.{w}) :=
  (Sheaf.adjunction K CommRingCat.adj).comp (Under.costarAdjForget A)

variable [hcolC : HasColimitsOfShape (Discrete WalkingPair) (Sheaf JC CommRingCat.{w})]
variable [hcolD : HasColimitsOfShape (Discrete WalkingPair) (Sheaf JD CommRingCat.{w})]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Inverse image commutes with the free algebra construction. -/
private def freeInverseImageIso (A : Sheaf JC CommRingCat.{w}) :
    f.inverseImage ⋙ Sheaf.composeAndSheafify JD CommRingCat.free ⋙
        Under.costar (f.commRingInverseImage.obj A) ≅
      Sheaf.composeAndSheafify JC CommRingCat.free ⋙ Under.costar A ⋙
        Under.post f.commRingInverseImage :=
  Adjunction.leftAdjointUniq
    ((f.adjunction.comp
        (freeForgetAdjunction (f.commRingInverseImage.obj A))).ofNatIsoRight
      (Functor.isoWhiskerLeft (Under.forget (f.commRingInverseImage.obj A))
        (commRingDirectImageForgetIso f).symm))
    ((freeForgetAdjunction A).comp
      (Under.postAdjunctionLeft (commRingInverseImageAdjunction f)))

variable [JC.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [JD.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [HasSheafify JC AddCommGrpCat.{w}] [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify JD AddCommGrpCat.{w}] [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {P B : Sheaf JC CommRingCat.{w}}

open CategoryTheory.Sheaf.InternalModule

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The underlying ring map induced by the unit of geometric inverse image. -/
private def ringUnitCarrier (P : Sheaf JC CommRingCat.{w}) :
    (sheafCompose JC (forget RingCat.{w})).obj (ringSheaf JC P) ⟶
      f.pushforward.obj ((sheafCompose JD (forget RingCat.{w})).obj
        (ringSheaf JD (f.commRingInverseImage.obj P))) :=
  f.adjunction.unit.app _ ≫
    f.pushforward.map (f.ringInverseImageForgetIso.inv.app (ringSheaf JC P)) ≫
    f.pushforward.map ((sheafCompose JD (forget RingCat.{w})).map
      (f.commRingInverseImageForgetRingIso.inv.app P))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The kernel inclusion followed by the unit on the ambient ring sheaf. -/
private def kernelUnitCarrier (α : P ⟶ B) :
    (ToInternal.underlying (ringSheaf JC P)).obj (KernelIdeal.sheaf α) ⟶
      f.pushforward.obj ((ToInternal.underlying
        (ringSheaf JD (f.commRingInverseImage.obj P))).obj
        (SheafOfModules.unit (ringSheaf JD (f.commRingInverseImage.obj P)))) :=
  (ToInternal.underlying (ringSheaf JC P)).map (KernelIdeal.ι α) ≫ ringUnitCarrier f P

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The ring-unit image of a kernel section is annihilated by the pulled-back quotient map. -/
private def kernelUnitCondition (α : P ⟶ B) : Prop :=
  kernelUnitCarrier f α ≫
      (ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj P)) ⋙
        f.pushforward).map (KernelIdeal.map (f.commRingInverseImage.map α)) =
    kernelUnitCarrier f α ≫
      (ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj P)) ⋙
        f.pushforward).map (0 : _ ⟶ _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The geometric adjunction unit restricted to the kernel ideal. -/
private def kernelUnit (α : P ⟶ B) (h : kernelUnitCondition f α) :
    (ToInternal.underlying (ringSheaf JC P)).obj (KernelIdeal.sheaf α) ⟶
      f.pushforward.obj ((ToInternal.underlying
        (ringSheaf JD (f.commRingInverseImage.obj P))).obj
          (KernelIdeal.sheaf (f.commRingInverseImage.map α))) := by
  let F := ToInternal.underlying (ringSheaf JD (f.commRingInverseImage.obj P))
  have forgetComposite : PreservesFiniteLimits
      (sheafCompose JD (forget AddCommGrpCat.{w}) ⋙
        sheafToPresheaf JD (Type w)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf JD AddCommGrpCat.{w} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w}))
    infer_instance
  have forgetful : PreservesFiniteLimits (sheafCompose JD (forget AddCommGrpCat.{w})) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have preserveF : PreservesFiniteLimits F := comp_preservesFiniteLimits
    (SheafOfModules.toSheaf _) (sheafCompose JD (forget AddCommGrpCat.{w}))
  have preservePush : PreservesFiniteLimits f.pushforward :=
    @PreservesLimits.preservesFiniteLimits _ _ _ _ f.pushforward
      f.adjunction.rightAdjoint_preservesLimits
  have preserveFG : PreservesFiniteLimits (F ⋙ f.pushforward) :=
    comp_preservesFiniteLimits F f.pushforward
  have preserve : PreservesLimit
      (parallelPair (KernelIdeal.map (f.commRingInverseImage.map α)) 0)
        (F ⋙ f.pushforward) :=
    @PreservesLimitsOfShape.preservesLimit _ _ _ _ _ _ (F ⋙ f.pushforward)
      (preserveFG.preservesFiniteLimits WalkingParallelPair) _
  let comparison := @PreservesEqualizer.iso _ _ _ _ (F ⋙ f.pushforward) _ _
    (KernelIdeal.map (f.commRingInverseImage.map α)) 0 inferInstance inferInstance preserve
  exact equalizer.lift (kernelUnitCarrier f α) h ≫ comparison.inv ≫
    (F ⋙ f.pushforward).map
      (kernelSubobjectIso (KernelIdeal.map (f.commRingInverseImage.map α))).inv

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The section map from the kernel ideal to its conormal quotient. -/
private def conormalQuotientApp {E : Type*} [Category* E]
    {K : GrothendieckTopology E} [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A B : Sheaf K CommRingCat.{w}} (α : A ⟶ B) (U : Eᵒᵖ)
    (x : (KernelIdeal.sheaf α).val.obj U) : (conormalSource α).val.obj U :=
  (conormalSourcePresheafUnit α).app U
    ((conormalIdeal α U).toCotangent ((KernelIdeal.sectionsIso α U).hom x))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The conormal quotient section maps commute with restriction. -/
private def conormalQuotientNaturality {E : Type*} [Category* E]
    {K : GrothendieckTopology E} [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget RingCat.{w})]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A B : Sheaf K CommRingCat.{w}} (α : A ⟶ B) : Prop :=
  ∀ {U V : Eᵒᵖ} (i : U ⟶ V),
    ((ToInternal.underlying (ringSheaf K A)).obj (KernelIdeal.sheaf α)).obj.map i ≫
        (↾fun x ↦ conormalQuotientApp α V x) =
      (↾fun x ↦ conormalQuotientApp α U x) ≫
        ((ToInternal.underlying (ringSheaf K B)).obj (conormalSource α)).obj.map i

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The natural map from kernel sections to conormal sections. -/
private def conormalQuotientCarrier {E : Type*} [Category* E]
    {K : GrothendieckTopology E} [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget RingCat.{w})]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A B : Sheaf K CommRingCat.{w}} (α : A ⟶ B) (h : conormalQuotientNaturality α) :
    (ToInternal.underlying (ringSheaf K A)).obj (KernelIdeal.sheaf α) ⟶
      (ToInternal.underlying (ringSheaf K B)).obj (conormalSource α) where
  hom := { app := fun U ↦ ↾fun x ↦ conormalQuotientApp α U x
           naturality := fun _ _ i ↦ h i }

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The kernel adjunction map followed by the conormal quotient map. -/
private def kernelConormalCarrier (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalSource (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hk : kernelUnitCondition f α)
    (hq : conormalQuotientNaturality (f.commRingInverseImage.map α)) :
    (ToInternal.underlying (ringSheaf JC P)).obj (KernelIdeal.sheaf α) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N :=
  kernelUnit f α hk ≫
    f.pushforward.map (conormalQuotientCarrier (f.commRingInverseImage.map α) hq) ≫ η

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The section map from the original kernel ideal to the direct image of the conormal quotient. -/
private def conormalKernelApp (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalSource (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hk : kernelUnitCondition f α)
    (hq : conormalQuotientNaturality (f.commRingInverseImage.map α))
    (U : Cᵒᵖ) (x : conormalIdeal α U) : ((restrictionAlong α).obj N).val.obj U :=
  (kernelConormalCarrier f α N η hk hq).hom.app U ((KernelIdeal.sectionsIso α U).inv x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The kernel-to-conormal section map is additive and linear and annihilates the square ideal. -/
private def conormalKernelConditions (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalSource (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hk : kernelUnitCondition f α)
    (hq : conormalQuotientNaturality (f.commRingInverseImage.map α)) : Prop :=
  (∀ U x y, conormalKernelApp f α N η hk hq U (x + y) =
    conormalKernelApp f α N η hk hq U x + conormalKernelApp f α N η hk hq U y) ∧
  (∀ U (r : P.obj.obj U) x, conormalKernelApp f α N η hk hq U (r • x) =
    r • conormalKernelApp f α N η hk hq U x) ∧
  (∀ U x y, conormalKernelApp f α N η hk hq U (x * y) = 0)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- A linear map annihilating the square ideal descends to the cotangent quotient. -/
private def cotangentLiftMap (R : CommRingCat.{w}) (I : Ideal R) (M : _root_.ModuleCat R)
    (g : I → M) (ha : ∀ x y, g (x + y) = g x + g y)
    (hs : ∀ (r : R) x, g (r • x) = r • g x)
    (hp : ∀ x y, g (x * y) = 0) : _root_.ModuleCat.of R I.Cotangent ⟶ M :=
  _root_.ModuleCat.ofHom (Ideal.Cotangent.lift
    { toFun := g, map_add' := ha, map_smul' := hs } hp)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The map on conormal quotient sections induced by the kernel-unit map. -/
private def conormalLiftApp (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalSource (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hk : kernelUnitCondition f α)
    (hq : conormalQuotientNaturality (f.commRingInverseImage.map α))
    (h : conormalKernelConditions f α N η hk hq) (U : Cᵒᵖ) :
    conormalObj α U ⟶ ((restrictionAlong α).obj N).val.obj U :=
  cotangentLiftMap (P.obj.obj U) (conormalIdeal α U) (((restrictionAlong α).obj N).val.obj U)
    (conormalKernelApp f α N η hk hq U) (h.1 U) (h.2.1 U) (h.2.2 U)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The descended conormal section maps commute with restriction. -/
private def conormalLiftNaturality (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalSource (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hk : kernelUnitCondition f α)
    (hq : conormalQuotientNaturality (f.commRingInverseImage.map α))
    (h : conormalKernelConditions f α N η hk hq) : Prop :=
  ∀ {U V : Cᵒᵖ} (i : U ⟶ V),
    (conormalPresheaf α).map i ≫
        (ModuleCat.restrictScalars (((ringSheaf JC P).obj.map i).hom)).map
          (conormalLiftApp f α N η hk hq h V) =
      conormalLiftApp f α N η hk hq h U ≫ ((restrictionAlong α).obj N).val.map i

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The sheafified map adjoint to the inverse-image conormal comparison. -/
private def conormalAdjoint (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalSource (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hk : kernelUnitCondition f α)
    (hq : conormalQuotientNaturality (f.commRingInverseImage.map α))
    (h : conormalKernelConditions f α N η hk hq)
    (hn : conormalLiftNaturality f α N η hk hq h) :
    conormalSource α ⟶ N :=
  ((extendRestrictAdj α).homEquiv _ _).symm
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf JC P).obj)).symm
      { app := fun U ↦ conormalLiftApp f α N η hk hq h U
        naturality := fun i ↦ hn i })

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical universal relative derivation on each section ring. -/
private def tensorDerivationApp {E : Type*} [Category* E]
    {K : GrothendieckTopology E} [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A P B : Sheaf K CommRingCat.{w}} (φ : A ⟶ P) (α : P ⟶ B)
    (U : Eᵒᵖ) (x : P.obj.obj U) : (conormalTensorTerm φ α).val.obj U :=
  ((extendRestrictAdj α).unit.app Ω(φ)).val.app U ((relativeDifferential φ).d x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The universal derivations commute with restriction of sections. -/
private def tensorDerivationNaturality {E : Type*} [Category* E]
    {K : GrothendieckTopology E} [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget RingCat.{w})]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A P B : Sheaf K CommRingCat.{w}} (φ : A ⟶ P) (α : P ⟶ B) : Prop :=
  ∀ {U V : Eᵒᵖ} (i : U ⟶ V),
    ((sheafCompose K (forget RingCat.{w})).obj (ringSheaf K P)).obj.map i ≫
        (↾fun x ↦ tensorDerivationApp φ α V x) =
      (↾fun x ↦ tensorDerivationApp φ α U x) ≫
        ((ToInternal.underlying (ringSheaf K B)).obj (conormalTensorTerm φ α)).obj.map i

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The natural underlying-sheaf map of the universal relative derivation. -/
private def tensorDerivationCarrier {E : Type*} [Category* E]
    {K : GrothendieckTopology E} [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [K.HasSheafCompose (forget RingCat.{w})]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A P B : Sheaf K CommRingCat.{w}} (φ : A ⟶ P) (α : P ⟶ B)
    (h : tensorDerivationNaturality φ α) :
    (sheafCompose K (forget RingCat.{w})).obj (ringSheaf K P) ⟶
      (ToInternal.underlying (ringSheaf K B)).obj (conormalTensorTerm φ α) where
  hom := { app := fun U ↦ ↾fun x ↦ tensorDerivationApp φ α U x
           naturality := fun _ _ i ↦ h i }

variable {A : Sheaf JC CommRingCat.{w}}

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The adjunction unit followed by the universal relative derivation. -/
private def tensorAdjointCarrier (φ : A ⟶ P) (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalTensorTerm (f.commRingInverseImage.map φ) (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hq : tensorDerivationNaturality (f.commRingInverseImage.map φ)
      (f.commRingInverseImage.map α)) :
    (sheafCompose JC (forget RingCat.{w})).obj (ringSheaf JC P) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N :=
  ringUnitCarrier f P ≫
    f.pushforward.map (tensorDerivationCarrier (f.commRingInverseImage.map φ)
      (f.commRingInverseImage.map α) hq) ≫ η

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The adjoint section map is a derivation relative to the base-ring map. -/
private def tensorAdjointConditions (φ : A ⟶ P) (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalTensorTerm (f.commRingInverseImage.map φ) (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hq : tensorDerivationNaturality (f.commRingInverseImage.map φ)
      (f.commRingInverseImage.map α)) : Prop :=
  let M := (restrictionAlong α).obj N
  let d : ∀ U : Cᵒᵖ, P.obj.obj U → M.val.obj U :=
    fun U x ↦ (tensorAdjointCarrier f φ α N η hq).hom.app U x
  (∀ U x y, d U (x + y) = d U x + d U y) ∧
  (∀ U x y, d U (x * y) = x • d U y + y • d U x) ∧
  (∀ U (a : A.obj.obj U), d U (φ.hom.app U a) = 0) ∧
  (∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : P.obj.obj U),
    d V (P.obj.map i x) = M.val.map i (d U x))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The linear map induced by the adjoint relative derivation. -/
private def tensorAdjoint (φ : A ⟶ P) (α : P ⟶ B)
    (N : SheafOfModules (ringSheaf JC B))
    (η : f.pushforward.obj ((ToInternal.underlying
      (ringSheaf JD (f.commRingInverseImage.obj B))).obj
        (conormalTensorTerm (f.commRingInverseImage.map φ) (f.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj N)
    (hq : tensorDerivationNaturality (f.commRingInverseImage.map φ)
      (f.commRingInverseImage.map α))
    (h : tensorAdjointConditions f φ α N η hq) :
    conormalTensorTerm φ α ⟶ N :=
  ((extendRestrictAdj α).homEquiv _ _).symm
    (relativeDifferentialDesc φ
      (PresheafOfModules.Derivation'.mk
        (fun U ↦ ModuleCat.Derivation.mk
          (fun x ↦ (tensorAdjointCarrier f φ α N η hq).hom.app U x)
          (h.1 U) (h.2.1 U) (h.2.2.1 U))
        (fun _ _ i x ↦ h.2.2.2 i x)))

variable {O : Sheaf JD CommRingCat.{w}}
variable (q : ToposHom (ofCommRingSheaf JD O) (ofCommRingSheaf JC B))
variable [(SheafOfModules.restrictScalars.{w} q.structureMap).IsRightAdjoint]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The conormal module of the inverse-image presentation, extended to the source structure sheaf. -/
private abbrev pulledConormal (α : P ⟶ B) :=
  (extendAlong (normalizedProjection q)).obj (conormalSource (q.toTopos.commRingInverseImage.map α))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The relative differentials of the inverse-image presentation, extended to the source structure sheaf. -/
private abbrev pulledTensor (φ : A ⟶ P) (α : P ⟶ B) :=
  (extendAlong (normalizedProjection q)).obj
    (conormalTensorTerm (q.toTopos.commRingInverseImage.map φ)
      (q.toTopos.commRingInverseImage.map α))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The carrier map induced by the scalar-adjunction unit on the pulled conormal module. -/
private def conormalPushCarrier (α : P ⟶ B) :
    q.toTopos.pushforward.obj ((ToInternal.underlying (ringSheaf JD (normalizedRing q))).obj
      (conormalSource (q.toTopos.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj (q.modulePushforward.obj (pulledConormal q α)) :=
  q.toTopos.pushforward.map
      ((ToInternal.underlying (ringSheaf JD (normalizedRing q))).map
        ((extendRestrictAdj (normalizedProjection q)).unit.app
          (conormalSource (q.toTopos.commRingInverseImage.map α)))) ≫
    (ModulePushforward.forgetIso q).inv.app (pulledConormal q α)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The carrier map induced by the scalar-adjunction unit on pulled relative differentials. -/
private def tensorPushCarrier (φ : A ⟶ P) (α : P ⟶ B) :
    q.toTopos.pushforward.obj ((ToInternal.underlying (ringSheaf JD (normalizedRing q))).obj
      (conormalTensorTerm (q.toTopos.commRingInverseImage.map φ)
        (q.toTopos.commRingInverseImage.map α))) ⟶
      (ToInternal.underlying (ringSheaf JC B)).obj (q.modulePushforward.obj (pulledTensor q φ α)) :=
  q.toTopos.pushforward.map
      ((ToInternal.underlying (ringSheaf JD (normalizedRing q))).map
        ((extendRestrictAdj (normalizedProjection q)).unit.app
          (conormalTensorTerm (q.toTopos.commRingInverseImage.map φ)
            (q.toTopos.commRingInverseImage.map α)))) ≫
    (ModulePushforward.forgetIso q).inv.app (pulledTensor q φ α)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Kernel, conormal, and derivation section maps satisfy their descent and naturality laws. -/
private def PresentationInverseImageLaws (φ : A ⟶ P) (α : P ⟶ B) : Prop :=
  kernelUnitCondition q.toTopos α ∧
  conormalQuotientNaturality (q.toTopos.commRingInverseImage.map α) ∧
  (∀ kernel quotient, conormalKernelConditions q.toTopos α
    (q.modulePushforward.obj (pulledConormal q α)) (conormalPushCarrier q α) kernel quotient) ∧
  (∀ kernel quotient linear, conormalLiftNaturality q.toTopos α
    (q.modulePushforward.obj (pulledConormal q α)) (conormalPushCarrier q α) kernel quotient linear) ∧
  tensorDerivationNaturality
    (q.toTopos.commRingInverseImage.map φ) (q.toTopos.commRingInverseImage.map α) ∧
  (∀ tensor_naturality, tensorAdjointConditions q.toTopos φ α
    (q.modulePushforward.obj (pulledTensor q φ α)) (tensorPushCarrier q φ α) tensor_naturality)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The conormal pullback map adjoint to the explicitly descended conormal map. -/
private def conormalForward (φ : A ⟶ P) (α : P ⟶ B)
    (h : PresentationInverseImageLaws q φ α) :
    q.modulePullback.obj (conormalSource α) ⟶ pulledConormal q α :=
  (q.moduleAdjunction.homEquiv _ _).symm
    (conormalAdjoint q.toTopos α (q.modulePushforward.obj (pulledConormal q α))
      (conormalPushCarrier q α) h.1 h.2.1 (h.2.2.1 h.1 h.2.1)
      (h.2.2.2.1 h.1 h.2.1 (h.2.2.1 h.1 h.2.1)))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The differential pullback map adjoint to the universal-derivation map. -/
private def tensorForward (φ : A ⟶ P) (α : P ⟶ B)
    (h : PresentationInverseImageLaws q φ α) :
    q.modulePullback.obj (conormalTensorTerm φ α) ⟶ pulledTensor q φ α :=
  (q.moduleAdjunction.homEquiv _ _).symm
    (tensorAdjoint q.toTopos φ α (q.modulePushforward.obj (pulledTensor q φ α))
      (tensorPushCarrier q φ α) h.2.2.2.2.1 (h.2.2.2.2.2 h.2.2.2.2.1))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The degreewise module pullback of the naive cotangent presentation complex. -/
private abbrev comparisonSource (φ : A ⟶ P) (α : P ⟶ B) :=
  q.modulePullbackComplex.obj (SheafOfModules.RingedSite.NaiveCotangent.Presentation.complex φ α)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The naive cotangent complex of the inverse-image presentation, extended to the source ring. -/
private abbrev comparisonTarget (φ : A ⟶ P) (α : P ⟶ B) :=
  (extendComplex (normalizedProjection q)).obj
    (SheafOfModules.RingedSite.NaiveCotangent.Presentation.complex
      (q.toTopos.commRingInverseImage.map φ) (q.toTopos.commRingInverseImage.map α))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The conormal map in degree minus one and the differential map in degree zero, with zero components elsewhere. -/
private def comparisonComponents (φ : A ⟶ P) (α : P ⟶ B)
    (h : PresentationInverseImageLaws q φ α) :
    ∀ i : ℤ, (comparisonSource q φ α).X i ⟶ (comparisonTarget q φ α).X i
  | Int.negSucc 0 => conormalForward q φ α h
  | Int.ofNat 0 => tensorForward q φ α h
  | Int.negSucc (_ + 1) => 0
  | Int.ofNat (_ + 1) => 0

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical free-algebra presentation commutes with geometric inverse image. -/
private def canonicalMiddleIso {S : Sheaf JC CommRingCat.{w}} (ψ : S ⟶ B) :
    FreeAlgebra.Presentation.obj (q.toTopos.commRingInverseImage.obj S)
      (Under.mk (q.toTopos.commRingInverseImage.map ψ)) ≅
      (Under.post q.toTopos.commRingInverseImage).obj (FreeAlgebra.Presentation.obj S (Under.mk ψ)) :=
  (Sheaf.composeAndSheafify JD CommRingCat.free ⋙
      Under.costar (q.toTopos.commRingInverseImage.obj S)).mapIso
      ((commRingInverseImageForgetIso q.toTopos).app B) ≪≫
    (freeInverseImageIso q.toTopos S).app (FreeAlgebra.Presentation.generators (Under.mk ψ))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The conormal and differential comparisons form a cochain map compatible with canonical free presentations. -/
private def CotangentInverseImageLaws (φ : A ⟶ P) (α : P ⟶ B) : Prop :=
  PresentationInverseImageLaws q φ α ∧
  (∀ h : PresentationInverseImageLaws q φ α, ∀ i j : ℤ,
    (comparisonSource q φ α).d i j ≫ comparisonComponents q φ α h j =
      comparisonComponents q φ α h i ≫ (comparisonTarget q φ α).d i j) ∧
  (∀ {S : Sheaf JC CommRingCat.{w}} (ψ : S ⟶ B),
    CommSq (𝟙 (q.toTopos.commRingInverseImage.obj S))
      (q.toTopos.commRingInverseImage.map (FreeAlgebra.Presentation.base S (Under.mk ψ)))
      (FreeAlgebra.Presentation.base (q.toTopos.commRingInverseImage.obj S)
        (Under.mk (q.toTopos.commRingInverseImage.map ψ))) (canonicalMiddleIso q ψ).inv.right) ∧
  (∀ {S : Sheaf JC CommRingCat.{w}} (ψ : S ⟶ B),
    CommSq (canonicalMiddleIso q ψ).inv.right
      (q.toTopos.commRingInverseImage.map (FreeAlgebra.Presentation.map S (Under.mk ψ)))
      (FreeAlgebra.Presentation.map (q.toTopos.commRingInverseImage.obj S)
        (Under.mk (q.toTopos.commRingInverseImage.map ψ))) (𝟙 (q.toTopos.commRingInverseImage.obj B)))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Inverse image transports conormal quotients and relative derivations compatibly with
presentation differentials and the canonical free-algebra comparisons. -/
private theorem cotangentInverseImageComparison_laws (φ : A ⟶ P) (α : P ⟶ B) :
    CotangentInverseImageLaws q φ α := sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The cochain map with the specified conormal and relative-differential components. -/
private def presentationComparison (φ : A ⟶ P) (α : P ⟶ B) :
    comparisonSource q φ α ⟶ comparisonTarget q φ α where
  f := comparisonComponents q φ α (cotangentInverseImageComparison_laws q φ α).1
  comm' := fun i j _ ↦ ((cotangentInverseImageComparison_laws q φ α).2.1
    (cotangentInverseImageComparison_laws q φ α).1 i j).symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical morphism from the inverse-image free presentation to the free presentation of the inverse image. -/
private def canonicalPresentationHom {S : Sheaf JC CommRingCat.{w}} (ψ : S ⟶ B) :
    SheafOfModules.RingedSite.NaiveCotangent.Presentation.Hom
      (q.toTopos.commRingInverseImage.map (FreeAlgebra.Presentation.base S (Under.mk ψ)))
      (q.toTopos.commRingInverseImage.map (FreeAlgebra.Presentation.map S (Under.mk ψ)))
      (FreeAlgebra.Presentation.base (q.toTopos.commRingInverseImage.obj S)
        (Under.mk (q.toTopos.commRingInverseImage.map ψ)))
      (FreeAlgebra.Presentation.map (q.toTopos.commRingInverseImage.obj S)
        (Under.mk (q.toTopos.commRingInverseImage.map ψ))) where
  base := 𝟙 _
  middle := (canonicalMiddleIso q ψ).inv.right
  target := 𝟙 _
  baseSq := (cotangentInverseImageComparison_laws q
    (FreeAlgebra.Presentation.base S (Under.mk ψ))
    (FreeAlgebra.Presentation.map S (Under.mk ψ))).2.2.1 ψ
  targetSq := (cotangentInverseImageComparison_laws q
    (FreeAlgebra.Presentation.base S (Under.mk ψ))
    (FreeAlgebra.Presentation.map S (Under.mk ψ))).2.2.2 ψ

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The ordinary pullback comparison for naive cotangent complexes, induced by inverse image of presentations. -/
def _root_.RingedSite.ToposHom.NaiveCotangent.underivedComparison {S : Sheaf JC CommRingCat.{w}} (ψ : S ⟶ B) :
    q.modulePullbackComplex.obj (SheafOfModules.RingedSite.NaiveCotangent.obj S (Under.mk ψ)) ⟶
      (extendComplex (normalizedProjection q)).obj
        (SheafOfModules.RingedSite.NaiveCotangent.obj (q.toTopos.commRingInverseImage.obj S)
          (Under.mk (q.toTopos.commRingInverseImage.map ψ))) :=
  presentationComparison q (FreeAlgebra.Presentation.base S (Under.mk ψ))
      (FreeAlgebra.Presentation.map S (Under.mk ψ)) ≫
    (extendComplex (normalizedProjection q)).map
      ((extendComplexIdIso _).inv.app _ ≫
        SheafOfModules.RingedSite.NaiveCotangent.Presentation.Hom.map (canonicalPresentationHom q ψ))


end InverseImage
end InverseImage

end RingedSite.ToposHom.NaiveCotangent
